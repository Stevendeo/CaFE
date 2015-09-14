type token =
  | PROP of (string)
  | TRUE
  | FALSE
  | INTERN
  | CALL of (string)
  | RETURN of (string)
  | NEXT
  | FATALLY
  | GLOBALLY
  | NOT
  | UNTIL
  | OR
  | AND
  | IMPLIES
  | EQUIV
  | GENERAL
  | ABSTRACT
  | PAST
  | L_PAREN
  | R_PAREN
  | EOF

open Parsing;;
let _ = parse_error;;
# 1 "formula_parser.mly"
 
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
# 269 "formula_parser.ml"
let yytransl_const = [|
  258 (* TRUE *);
  259 (* FALSE *);
  260 (* INTERN *);
  263 (* NEXT *);
  264 (* FATALLY *);
  265 (* GLOBALLY *);
  266 (* NOT *);
  267 (* UNTIL *);
  268 (* OR *);
  269 (* AND *);
  270 (* IMPLIES *);
  271 (* EQUIV *);
  272 (* GENERAL *);
  273 (* ABSTRACT *);
  274 (* PAST *);
  275 (* L_PAREN *);
  276 (* R_PAREN *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* PROP *);
  261 (* CALL *);
  262 (* RETURN *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\003\000\004\000\004\000\004\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\000\000"

let yylen = "\002\000\
\002\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\003\000\001\000\001\000\002\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\004\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\005\000\006\000\007\000\010\000\011\000\000\000\
\000\000\000\000\000\000\000\000\021\000\000\000\008\000\002\000\
\003\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\
\009\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yydgoto = "\002\000\
\013\000\014\000\019\000\015\000"

let yysindex = "\255\255\
\040\255\000\000\000\000\000\000\000\000\000\000\000\000\010\255\
\010\255\010\255\040\255\040\255\000\000\019\000\000\000\000\000\
\000\000\000\000\040\255\040\255\040\255\041\255\000\255\010\255\
\040\255\040\255\040\255\040\255\000\000\041\255\041\255\041\255\
\000\000\040\255\041\255\041\255\041\255\041\255\041\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\002\000\003\000\004\000\
\000\000\000\000\005\000\006\000\007\000\008\000\009\000"

let yygindex = "\000\000\
\000\000\010\000\015\000\000\000"

let yytablesize = 290
let yytable = "\001\000\
\012\000\015\000\013\000\014\000\016\000\017\000\018\000\019\000\
\020\000\000\000\024\000\025\000\026\000\027\000\028\000\000\000\
\000\000\000\000\029\000\033\000\022\000\023\000\000\000\020\000\
\021\000\016\000\017\000\018\000\030\000\031\000\032\000\000\000\
\000\000\000\000\035\000\036\000\037\000\038\000\034\000\000\000\
\003\000\004\000\005\000\039\000\006\000\007\000\008\000\009\000\
\010\000\011\000\000\000\024\000\025\000\026\000\027\000\028\000\
\000\000\000\000\012\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\012\000\015\000\013\000\014\000\
\016\000\017\000\018\000\019\000\020\000\024\000\025\000\026\000\
\027\000\028\000"

let yycheck = "\001\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\255\255\011\001\012\001\013\001\014\001\015\001\255\255\
\255\255\255\255\000\000\020\001\011\000\012\000\255\255\009\000\
\010\000\016\001\017\001\018\001\019\000\020\000\021\000\255\255\
\255\255\255\255\025\000\026\000\027\000\028\000\024\000\255\255\
\001\001\002\001\003\001\034\000\005\001\006\001\007\001\008\001\
\009\001\010\001\255\255\011\001\012\001\013\001\014\001\015\001\
\255\255\255\255\019\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\020\001\020\001\020\001\020\001\
\020\001\020\001\020\001\020\001\020\001\011\001\012\001\013\001\
\014\001\015\001"

let yynames_const = "\
  TRUE\000\
  FALSE\000\
  INTERN\000\
  NEXT\000\
  FATALLY\000\
  GLOBALLY\000\
  NOT\000\
  UNTIL\000\
  OR\000\
  AND\000\
  IMPLIES\000\
  EQUIV\000\
  GENERAL\000\
  ABSTRACT\000\
  PAST\000\
  L_PAREN\000\
  R_PAREN\000\
  EOF\000\
  "

let yynames_block = "\
  PROP\000\
  CALL\000\
  RETURN\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 271 "formula_parser.mly"
             (_1)
# 447 "formula_parser.ml"
               : Caretast.caret_formula))
; (fun __caml_parser_env ->
    Obj.repr(
# 275 "formula_parser.mly"
           (General)
# 453 "formula_parser.ml"
               : 'opkind))
; (fun __caml_parser_env ->
    Obj.repr(
# 277 "formula_parser.mly"
            (Abstract)
# 459 "formula_parser.ml"
               : 'opkind))
; (fun __caml_parser_env ->
    Obj.repr(
# 279 "formula_parser.mly"
        (Past)
# 465 "formula_parser.ml"
               : 'opkind))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 284 "formula_parser.mly"
  ((CProp ((parse_formula _1), (cvc_string _1))))
# 472 "formula_parser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    Obj.repr(
# 286 "formula_parser.mly"
  (CTrue)
# 478 "formula_parser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    Obj.repr(
# 288 "formula_parser.mly"
  (CFalse)
# 484 "formula_parser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'predicate) in
    Obj.repr(
# 292 "formula_parser.mly"
  (_1)
# 491 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 294 "formula_parser.mly"
  (_2)
# 498 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 297 "formula_parser.mly"
     (CInfo (ICall (let s = String.trim _1 in 
			   if s  = "" then None else (Some s))))
# 506 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 301 "formula_parser.mly"
     (CInfo (IRet (let s = String.trim _1 in 
			   if s  = "" then None else (Some s))))
# 514 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 305 "formula_parser.mly"
  (Caretast.CNot _2)
# 521 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'opkind) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 307 "formula_parser.mly"
  (Caretast.CFatally (_2,_3))
# 529 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'opkind) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 309 "formula_parser.mly"
  (Caretast.CGlobally (_2, _3))
# 537 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'opkind) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 311 "formula_parser.mly"
  (Caretast.CNext (_2, _3))
# 545 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 313 "formula_parser.mly"
  (Caretast.COr (_1,_3))
# 553 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 315 "formula_parser.mly"
  (Caretast.CAnd (_1,_3))
# 561 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 317 "formula_parser.mly"
  (Caretast.CImplies (_1,_3))
# 569 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 319 "formula_parser.mly"
  (Caretast.CIff (_1,_3))
# 577 "formula_parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'opkind) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 321 "formula_parser.mly"
  (Caretast.CUntil (_3,_1,_4))
# 586 "formula_parser.ml"
               : 'formula))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Caretast.caret_formula)
