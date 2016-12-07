%{ 
open Caretast 
open Logic_typing

let dkey = Caret_option.register_category "parser" 

let parse_formula str = 
  let str = String.trim (String.sub str 1 ((String.length str) - 2)) in
  
  try 
    let lexbuf = Lexing.from_string str in
    
    Caret_option.debug 
      ~dkey 
      "%s lexed successfully"
      str;
    
    let lexpr = 
      Logic_parser.lexpr_eof Logic_lexer.token lexbuf 
    in
    Caret_option.debug 
      ~dkey 
      "%s logic_parsed successfully"
      str;
    
    let res = Formula_typer.Typer.predicate (Lenv.empty ()) lexpr
    in
    Caret_option.debug 
      ~dkey 
      "%s parsed successfully !"
      str;
    res
  with
    Parsing.Parse_error -> 
      failwith 
	("Error during the formula parsing, " 
	 ^ str 
	 ^ " is an incorrect predicate.")
(*
let pred_to_cvc pred = 
  let open Cil_datatype in 

  let logic_vars = 
    Logic_var.Hashtbl.create 5
  in

  let term_unop = function 
  
    Neg   -> "-"
  | BNot  -> "~"
  | LNot  -> "NOT"
  in
 
  let term_binop = function
    | PlusA | PlusPI | IndexPI -> " + "   (** arithmetic + *)
    | MinusA | MinusPI | MinusPP ->  " - "
    | Mult -> " * "
    | Div -> " / " 
    | Mod  -> assert false
    | Shiftlt -> " << " 
    | Shiftrt -> " >> " 
    | Lt -> "<"      
    | Gt -> ">"  
    | Le -> "<="    
    | Ge  -> ">="
    | Eq  -> "=="  
    | Ne  -> "/="
    | BAnd -> " & "
    | BXor -> assert false
    | BOr -> " | "

    | LAnd | LOr -> assert false     
  (** logical or. Unlike other expressions this one does not always
      evaluate both operands.  If you
      want to use these, you must set
      {!Cil.useLogicalOperators}. *)
  in
  let rec str_term = function
  
    | TConst cst -> 
      match cst with
	Integer (i,_) -> string_of_int i
      | TLval (t_lhost, _ )-> 
	begin (* TLval *)
	  match t_lhost with
	  | TVar v -> 
	    begin (* TVar *)
	      
	      try Logic_var.Hashtbl.find logic_vars v 
	      with
		Not_found -> 
		  let res = v.lv_name in 
		  let () = Logic_var.Hashtbl.add logic_vars v res 
		  in res
		  
	    end (* TVar *)
	  | TResult _ -> 
	    Caret_option.abort 
	      "Results of a call cannot be expressed in a predicate (yet)"
	      
	  | TMem t -> str_term t
	end(* TLval *)
          
      | TUnOp (uop,term) ->
	term_unop uop ^ "(" ^ str_term ^ ")"

    | TSizeOf _ | TSizeOfE _ | TSizeOfStr _ | TAlignOf _ | TAlignOfE 
      -> assert false
      
    | TBinOp (bop,t1,t2) -> 
      "(" ^(str_term t1)^ ")" ^ term_binop bop ^ "(" ^(str_term t2) ^ ")"
	
    | TCastE _ | TAddrOf _ | TStartOf _ -> assert false
    
    
    
  in

  let str_rel = function 
  
  | Rlt -> "<"
  | Rgt -> ">"
  | Rle -> "<="
  | Rge -> "=>"
  | Req -> "="
  | Rneq -> "/="
  in
  
  let rec __pred_to_cvc pred = 
    
    let res =  
    | Pfalse -> "false"
    | Ptrue -> "true"
    | Papp _ | Pseparated _ | Plet _ -> assert false 
      
    | Prel (rel,t1,t2) -> 
      let s_rel = str_rel rel in 
      
      (str_term t1) ^ s_rel ^ (str_term t2)
  
    | Pand (p1, p2) -> 
      (__pred_to_cvc p1.content) ^ " AND " ^ (__pred_to_cvc p2.content)
        
    | Por (p1, p2) -> 
      (__pred_to_cvc p1.content) ^ " OR " ^ (__pred_to_cvc p2.content)

    | Pxor (p1, p2) -> 
      (__pred_to_cvc p1.content) ^ " XOR " ^ (__pred_to_cvc p2.content)

    | Pimplies (p1, p2) -> 
      (__pred_to_cvc p1.content) ^ " => " ^ (__pred_to_cvc p2.content)
	
    | Piff (p1, p2) -> 
      (__pred_to_cvc p1.content) ^ " <=> " ^ (__pred_to_cvc p2.content)
	
    | Pnot p -> 
      " NOT( "^ (__pred_to_cvc p) ^ ")"

    | Pif (t,p1,p2) ->
      "IF " ^ (str_term t) ^ 
	" THEN " ^ (__pred_to_cvc p1.content) ^ 
	" ELSE " ^ (__pred_to_cvc p2.content) ^ 
	" ENDIF"
	
    | Pforall (qt, p) -> 
      "FORALL (" ^ 
      
      of quantifiers * predicate named (** universal quantification. *)
    | Pexists of quantifiers * predicate named (** existential quantification. *)
  | Pat of predicate named * logic_label
  (** predicate refers to a particular program point. *)
  | Pvalid_read of logic_label * term   (** the given locations are valid for reading. *)
  | Pvalid of logic_label * term   (** the given locations are valid. *)
  (** | Pvalid_index of term * term
      {b deprecated:} Use [Pvalid(TBinOp(PlusPI,p,i))] instead.
          [Pvalid_index(p,i)] indicates that accessing the [i]th element
          of [p] is valid.
      | Pvalid_range of term * term * term
       {b deprecated:} Use [Pvalid(TBinOp(PlusPI(p,Trange(i1,i2))))] instead.
          similar to [Pvalid_index] but for a range of indices.*)
  | Pinitialized of logic_label * term   (** the given locations are initialized. *)
  | Pdangling of logic_label * term (** the given locations contain dangling
                                        adresses. *)
  | Pallocable of logic_label * term   (** the given locations can be allocated. *)
  | Pfreeable of logic_label * term   (** the given locations can be free. *)
  | Pfresh of logic_label * logic_label * term * term
      (** \fresh(pointer, n)
	  A memory block of n bytes is newly allocated to the pointer.*)
  | Psubtype of term * term
      (** First term is a type tag that is a subtype of the second. *)
 
    in
    "\\(" ^ res ^ "\\)"
*)
(** Transforms an "ACSL" string into a "CVC3" string. *)
let cvc_string str = 
  let () = Caret_option.debug ~dkey "parsing %s into cvc format" str in
  let i = ref 0 in

  let first_str = 
  String.map
    (fun c ->  
      let () = i := !i + 1 in
      match c with
	'!' -> if str.[!i] = '=' then '/' else '!'
      | '=' -> if  str.[!i] = '=' then ' ' else c
      (*| '|' ->  if  str.[!i] = '|' then 'O' else 'R'*)
      |'\\' | '[' | ']' -> '_'
      | '(' | ')'| '{' | '}' -> ' '
      | _ -> c
    )
    str

  in
  let rec lower acc index str = 
    try 
      let next_l = 
	String.index_from str index '<'
      in
    lower
      (acc ^ (String.sub 
		str 
		index 
		(next_l - index) 
       )
       ^ " \\< ")
      (next_l + 1)
      str
    with
      Not_found -> 
	acc 
	^ (String.sub 
	     str 
	     index 
	     ((String.length str) - index) )
  in
  let res = 
  lower "" 0 first_str
  in
  
  Caret_option.debug ~dkey "Res : %s" res ; res
%}

/* Atomic propositions  */
%token <string> PROP
%token TRUE FALSE INTERN
%token <string> CALL
%token <string> RETURN

/* Unary operators  */
%token NEXT FATALLY GLOBALLY
%token NOT

/* Binary operators */
%token UNTIL 
%token OR AND IMPLIES EQUIV

/* Qualificators of CaRet operators */
%token GENERAL ABSTRACT PAST

/* Additionnal tokens */
%token L_PAREN R_PAREN
%token EOF

%token UNTIL OR AND IMPLIES EQUIV
%right NOT NEXT FATALLY GLOBALLY
%start main
%type <Caretast.caret_formula> main
%%
main : 
	formula EOF {$1}
;

opkind : 
	| GENERAL {General}

	| ABSTRACT {Abstract}

	| PAST {Past}
;

predicate : 
	| PROP 		
		{(CProp (Logic_const.new_predicate (parse_formula $1), (cvc_string $1)))}
	| TRUE 		
		{CTrue}
	| FALSE 	
		{CFalse}
	
formula :
	| predicate
		{$1}
	| L_PAREN formula R_PAREN 
		{$2}

	| CALL 
	    {CInfo (ICall (let s = String.trim $1 in 
			   if s  = "" then None else (Some s)))}

	| RETURN	
	    {CInfo (IRet (let s = String.trim $1 in 
			   if s  = "" then None else (Some s)))}

	| NOT formula 
		{Caretast.CNot $2}
	| FATALLY opkind formula 
		{Caretast.CFatally ($2,$3)}
	| GLOBALLY opkind formula 
		{Caretast.CGlobally ($2, $3)}
	| NEXT opkind formula 
		{Caretast.CNext ($2, $3)}
	| formula OR formula 
		{Caretast.COr ($1,$3)}
	| formula AND formula 
		{Caretast.CAnd ($1,$3)}
	| formula IMPLIES formula 
		{Caretast.CImplies ($1,$3)}
	| formula EQUIV formula
		{Caretast.CIff ($1,$3)}
	| formula UNTIL opkind formula 
		{Caretast.CUntil ($3,$1,$4)}


