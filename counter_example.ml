open Cil_types
open Cil_datatype
open Rsmast
open Formula_datatype
open Caretast
open Cil
open Logic_const
open Smt_solver

open Type_RState
open Type_Rsm_module
 
let dkey = Caret_option.register_category "counter_example:back_dataflow"

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
  
  let () = 
    Caret_option.debug ~dkey
      "Predicate studied : %a"
      Printer.pp_predicate first_order_predicate
  in let vars = ref Logic_var.Set.empty (* These are the variables contained in the predicate *)
  in
  let registers_vars = 
      object
	inherit Visitor.frama_c_inplace
	  
	method! vvrbl v = 
	  vars := Logic_var.Set.add (Cil.cvar_to_lvar v) !vars; DoChildren
	   
      end
  in
  let () = 
    ignore (Cil.visitCilPredicate (registers_vars :> Cil.cilVisitor) (first_order_predicate) )
  in
  let () = 
    Back_dataflow.CafeStartData.clear () in
  let init_data = (first_order_predicate,Logic_var.Set.elements !vars) in
  let () = 
    Back_dataflow.CafeStartData.add s.s_stmt init_data in
  let () = (* crucial step : registers every block in the file. *)
    let v = Back_dataflow.block_registerer ()
    in
    Cil.visitCilFile (v :> Cil.cilVisitor) (Ast.get ())
  in
  let module Pred_Cafe_Backward = 
	Back_dataflow.Cafe_Backward 
	  (struct let pred = init_data end) in 
  let () = 
    Caret_option.debug ~dkey
      "Starting back dataflow computation..."  in
  let () = 
    Pred_Cafe_Backward.compute [s.s_stmt]
  in  
  let () = 
    Caret_option.debug ~dkey
      "Back dataflow done."  in
  let entry = 
    let main = (!Parameter_builder.find_kf_by_name "main") in
    match main.fundec with
      Definition(fdec,_) ->
	let () = Cfg.prepareCFG fdec
	in
	List.hd (fdec.sbody.bstmts)
    | _ -> Caret_option.log "CaFE does not work on non defined function. Exit."; assert false
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
      ~dkey
      "Predicate generated : @[%a@]"
      Printer.pp_predicate 
      pred
  in
    
  let answer = try z3_answer ~vars pred with 
      Smt_query_failure -> 
	let () = 
	  Caret_option.feedback "Error in SMT query." in
	  Unknown
  in
  
  Caret_option.debug ~dkey "%s" 
    (match answer with 
      Sat -> "Sat"
    | Unsat -> "Unsat"
    | Unknown -> "Unknown"
	
    );
  
  answer

let moduleTestAcceptance mdl = 
  let good_atoms = ref Atoms.Atom.Set.empty in
  let bad_atoms = ref Atoms.Atom.Set.empty in
  RState.Set.iter
    (fun state -> 
       let isret = match state.s_stmt.skind with Return _ -> true | _ -> false in
       if isret 
       then 
         let to_delete = 
         if Atoms.Atom.Set.mem state.s_atom !bad_atoms
         then true 
         else if Atoms.Atom.Set.mem state.s_atom !good_atoms
         then false 
         else 
           let () = 
             Caret_option.debug ~dkey
               "Can state %a with atom %a end the module %a ?"
               RState.pretty state
               Atoms.Atom.pretty state.s_atom
               Rsmast.Rsm_module.pretty mdl
           in
           begin 
             match backward_dataflow_from_state state with 
               Unsat -> 
               let () = bad_atoms := Atoms.Atom.Set.add state.s_atom !bad_atoms in
               true 
             | _ -> 
               let () = good_atoms := Atoms.Atom.Set.add state.s_atom !good_atoms in
               false 
                 
           end in
           if to_delete 
           then
             let () = 
               Caret_option.feedback "Deleting %a"
	         RState.pretty state	  
             in
             Rsm.deleteRState state) 
    mdl.states
  
let testAcceptance rsm = moduleTestAcceptance (Rsm.getMainMod rsm)
