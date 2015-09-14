open Formula_datatype
open Cil_types
open Caretast
(** Translates a Set of predicate into a cvc3 formula *)

let dkey = Caret_option.register_category "smt_solv"

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
  "prop: BOOLEAN = EXISTS\\(__cafe_tmp__:INT" ^ cvc_prefix  ^ "\\):" ^
    (
      Id_Formula.Set.fold 
	(fun itm acc -> 
	  (Caret_print.string_formula itm.form)  ^ " AND " ^ acc)
	set
	"__cafe_tmp__ = 0\\; CHECKSAT prop\\;"
      )
  
      
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
     	 
