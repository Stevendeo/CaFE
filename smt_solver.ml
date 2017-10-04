open Formula_datatype
open Cil_types
open Cil_datatype
open Cil
(** Translates a Set of predicate into a cvc3 formula *)

let dkey = Caret_option.register_category "smt_solv"
let dkey_z3 = Caret_option.register_category "formula_utils:z3"


let read_file chan =
  let lines = ref [] in
  try
    while true; do
      lines := input_line chan :: !lines
    done; 
    List.fold_right
      (fun str acc -> acc ^ str ^ "\n") 
      !lines 
      ""
  with End_of_file ->
    List.fold_right
      (fun str acc -> acc ^ str ^ "\n") 
      !lines ""

exception Smt_query_failure

let string_typ = function 
  | TInt _ -> "TFloat"
  | TFloat _ -> "TFloat"
  | TVoid _ -> "TVoid"
  | TPtr _ -> "TPtr"
  | TArray _ -> "TArray"
  | TFun _ -> "TFun"
  | TNamed _ -> "TNamed"
  | TComp _ -> "TComp"
  | TEnum _ -> "TEnum"
  | TBuiltin_va_list _ -> "TBuiltin_va_list"

let cvcParser set = 
  let cvc_prefix = 
      let rec whichType typ = match typ with 
	| TNamed (t_info,_) -> whichType t_info.ttype
	| _ -> typ
      in
      let main_vars = 
	 
	List.fold_left
	  (fun acc var -> 
	    match whichType var.vtype with
	      TInt _ -> 
		(","
		 ^ var.vname 
		 ^ ":INT" 
		 ^ acc)
	    | TFloat _ -> ","^ var.vname ^ ":REAL" ^ acc 
	    | _ -> 
	      Caret_option.debug ~dkey 
		"local var %s is a %s" var.vname (string_typ var.vtype); 
	      acc
	  )
	  ""
	  (Kernel_function.get_locals (Globals.Functions.find_by_name "main"))
      in
      
      Globals.Vars.fold
	(fun var _ acc -> 
	  Caret_option.debug ~dkey "var %s" var.vname; 
	  match whichType var.vtype with
	    TInt _ -> ","^ var.vname ^ ":INT" ^ acc
	  | TFloat _ -> ","^ var.vname ^ ":REAL" ^ acc 
	  | _ -> 
	    Caret_option.debug ~dkey "var %s is a %s" var.vname 
	      (string_typ var.vtype); 
	    acc
	      
	)
        main_vars      
  in 
  Format.fprintf 
    Format.str_formatter
    "prop: BOOLEAN = EXISTS\\__cafe_tmp__:INT %s \\):%a AND __cafe_tmp__ = 0 \\; CHECKSAT prop\\;"
    cvc_prefix 
    (Format.pp_print_list Id_Formula.pretty) (Id_Formula.Set.elements set)
    ;
    Format.flush_str_formatter ()
(*"prop: BOOLEAN = EXISTS\\(__cafe_tmp__:INT" ^ cvc_prefix  ^ "\\):" ^
    (
      Id_Formula.Set.fold 
	(fun itm acc -> 
	  (Caret_print.string_formula itm.form)  ^ " AND " ^ acc)
	set
	"__cafe_tmp__ = 0\\; CHECKSAT prop\\;"
      )
  *)
      
let cvcTest set = 
  let str_formula = cvcParser set in

  let echo_cmd = "echo " ^ str_formula  ^ " > __smt_cafe_tmp.cvc" in 
  let cvc_cmd = "cvc3 __smt_cafe_tmp.cvc > __smt_res.txt" in
  Caret_option.debug ~dkey  "echo command : %s" echo_cmd;
  Caret_option.debug ~dkey  "cvc3 command : %s" cvc_cmd;

  if Sys.command echo_cmd <> 0
  then  Caret_option.abort "failed to run cvc3 : echo failed"
  else 
    let () = Caret_option.debug ~dkey "echo ok" in
    
    if Sys.command cvc_cmd <> 0
    then Caret_option.abort "failed to run cvc3"
    else 
      let () = Caret_option.debug ~dkey "cvc3 ok" in
      
      let file = open_in "__smt_res.txt" in
      let result = input_line file in 
      let () = close_in file in
      result.[0] <> 'U'(* Unsatisfiable *)
     	 

type smt_answer = 
| Sat 
| Unsat 
| Unknown
     

let smt_query smt_solver options query = 
  
    let prefix_command = 
      List.fold_left
	(fun acc option -> 
	  acc  ^ " -" ^ option)
	smt_solver
	options 
    in
    
    let query_file = "__" ^ smt_solver ^ "_query.smt"
    in
    
    let answer_file = "__" ^ smt_solver ^ "_ans.txt"
    in
    
    let query_out = open_out query_file
    in
    let () = 
      Printf.fprintf query_out "%s\n" query;
      close_out query_out
    in
    
    let smt_command = 
      prefix_command  ^ " " ^ query_file  ^ " > "  ^  answer_file in
    
    if Sys.command smt_command <> 0
    then
      let () = 
	Caret_option.feedback "Command line %s failed" smt_command in 
      raise Smt_query_failure 
    else
      let file = open_in answer_file in
      let result = read_file file in 
      let () = close_in file in
      result

let z3_answer ?(vars = []) p = 

  let vars = 
    if vars <> []
    then vars
    else (* We visit the predicate and register every logic variable *)
      let lvars = ref Logic_var.Set.empty in
      let lvar_vis = 
        object
	  inherit Visitor.frama_c_inplace
	  method! vlogic_var_use lv = 
	    lvars := Logic_var.Set.add lv !lvars; Cil.DoChildren
	end
    
      in
      ignore(Cil.visitCilPredicate (lvar_vis :> Cil.cilVisitor) p);
      Logic_var.Set.elements !lvars 
  in
  let nlsat_query = 
    Pred_printer.predicate_to_smt_query p "qfnra-nlsat"
  in
  
  let basic_query = 
    Pred_printer.predicate_to_smt_query p ""
  in
  let q_with_model q = 
    List.fold_left
      (fun acc lvar ->  
	acc ^ "\n(get-value (" ^ lvar.Cil_types.lv_name ^"))")
      q
      vars
  in


    let res = (smt_query "z3" ["smt2"]  basic_query)
    in
    match String.lowercase_ascii (String.sub res 0 3) with
      "sat" -> begin
	let () = 
	  Caret_option.debug ~dkey:dkey_z3 
	    "%s!"
	    res
	in
	  
        Sat
      end
    | "uns" -> Unsat
    | "unk" ->  
      begin
	let () = 
	  Caret_option.feedback
	    "Can't say if satisfiable : trying a different option";
	 
	    Caret_option.debug ~dkey:dkey_z3 
	      "%s"
	      res
	in 
	let next_res = (smt_query "z3" ["smt2"] nlsat_query)
	in
	match String.lowercase_ascii (String.sub next_res 0 3) with
	  
	  "sat" ->
	    Caret_option.debug ~dkey:dkey_z3 
	      "%s"
	      next_res ; Sat
	
	| "uns" -> Unsat
	| "unk" -> 
	  let () = 
	    Caret_option.feedback "Can't say if satisfiable" ; 
	    try
	      let model = (smt_query "z3" ["smt2"] (q_with_model nlsat_query))
	      in
	      
	      Caret_option.debug ~dkey:dkey_z3 
		"%s"
		model
	    with
	      _ -> ()
	  in Unknown
	| _ -> Caret_option.fatal "?? : %s" next_res
      end
    | _ -> Caret_option.fatal "? : %s" res

let pred_mem lvar pred = 
  let lvar_vis = 
object
  inherit Visitor.frama_c_inplace
  method! vlogic_var_use lv = 
    if Logic_var.equal lv lvar
    then 
      let () = failwith "true" in SkipChildren
    else DoChildren
end
  in
  try ignore(Cil.visitCilPredicate (lvar_vis :> Cil.cilVisitor) pred);false
  with 
    Failure s -> if s = "true" then true else failwith s
      
