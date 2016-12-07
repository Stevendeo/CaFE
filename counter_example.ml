open Cil_types
open Cil_datatype
open Rsmast
open Formula_datatype
open Caretast
open Cil
open Logic_const
open Rsm

open Type_RState
open Type_Rsm_module

type smt_answer = 
| Sat 
| Unsat 
| Unknown

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
      !lines 
      ""

let dkey_z3 = Caret_option.register_category "counter_example:z3"

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
    then Caret_option.abort "Command line %s failed" smt_command
    else
      let file = open_in answer_file in
      let result = read_file file in 
      let () = close_in file in
      result

let z3_answer p vars = 

  let nlsat_query = 
    Pred_printer.predicate_to_smt_query p "qfnra-nlsat"
  in
  
  let basic_query = 
    Pred_printer.predicate_to_smt_query p ""
  in
  let q_with_model q = 
    List.fold_left
      (fun acc lvar ->  
	acc ^ "\n(get-value (" ^ lvar.lv_name ^"))")
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


let backward_dataflow_from_state s = 
  let first_order_predicate = (* Here is the predicate we will study *) 
    let unfold_formula p = 
      let rec neg_unfold is_neg p = 
	match p with CNot p -> neg_unfold (not is_neg) p
	| _ -> (is_neg,p)
      in
      neg_unfold false p
    in

    let rec caret_prop_to_predicate p = match p with
      	CProp (p,_) -> p.ip_content
      | CTrue -> unamed Ptrue
      | CFalse -> unamed Pfalse

      | CNot _ -> 
	let neg,prop = unfold_formula p
	in
	if neg then unamed (Pnot (caret_prop_to_predicate prop))
	else caret_prop_to_predicate prop
	
      | _ -> 
	Caret_option.abort "Property %a not supported"
	  Formula_datatype.Caret_Formula.pretty p
    in
    Id_Formula.Set.fold
      (fun prop acc -> 
	unamed (Pand (acc, caret_prop_to_predicate prop.form))
	
      )
      (Atoms_utils.atomicProps s.s_atom)
      (unamed Ptrue)
  in
  
  let vars = ref Logic_var.Set.empty (* These are the variables contained in the predicate *)
  in
  let registers_vars = 
      object
	inherit Visitor.frama_c_inplace
	  
	method! vvrbl v = 
	  vars := Logic_var.Set.add (Cil.cvar_to_lvar v) !vars; DoChildren
	   
      end
  in
  let () = 
    ignore (Cil.visitCilPredicate (registers_vars :> Cil.cilVisitor) (first_order_predicate) )in
  
  let init_data = (first_order_predicate,Logic_var.Set.elements !vars) in
  let () = 
    Back_dataflow.CafeStartData.add s.s_stmt init_data
  in
  let () = (* crucial step : registers every block in the file. *)
    let v = Back_dataflow.block_registerer ()
    in
    Cil.visitCilFile (v :> Cil.cilVisitor) (Ast.get ())
  in
  let module Pred_Cafe_Backward = 
	Back_dataflow.Cafe_Backward 
	  (struct let pred = init_data end) in
  let () = 
    Pred_Cafe_Backward.compute [s.s_stmt]
  in  
  let entry = 
    let main = (!Parameter_builder.find_kf_by_name "main") in
    match main.fundec with
      Definition(fdec,_) ->
	let () = Cfg.prepareCFG fdec
	in
	List.hd (fdec.sbody.bstmts)
    | _ -> assert false
  in
  let pred,vars = 
    try  
      Back_dataflow.CafeStartData.find entry
    with 
      Not_found ->
	Caret_option.fatal "Dataflow stopped before the first statement"
  in
  let () = 
    Caret_option.debug 
      ~dkey:dkey_z3
      "Predicate generated : @[%a@]"
      Printer.pp_predicate 
      pred
  in
    
  let answer = z3_answer pred vars
  in
  
  Caret_option.feedback "%s" 
    (match answer with 
      Sat -> "Sat"
    | Unsat -> "Unsat"
    | Unknown -> "Unknown"
	
    );
  
  answer

let testAcceptance rsm = 

  let main = Rsm.getMainMod rsm in 
  
  RState.Set.iter
    (fun state -> match state.s_stmt.skind with
      Cil_types.Return _ -> 
	begin 
	  match backward_dataflow_from_state state with 
	  Unsat -> Rsm.deleteRState state
	  | _ -> ()
	end
    | _ -> ()
    ) main.states
  
  
