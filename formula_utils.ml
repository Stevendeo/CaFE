open Caretast
open Formula_datatype
open Atoms
open Atoms_utils
open Cil_datatype
open Cil

(** Main steps of the construction of the properties following the possible 
    rgba paths *)

exception Unsatisfiable_formula
exception Smt_query_failure

module Fid = State_builder.SharedCounter(struct let name = "fid_counter" end)

let (spurious_stmt_hashtbl: Id_Formula.Set.t Cil_datatype.Stmt.Hashtbl.t)
    = Cil_datatype.Stmt.Hashtbl.create 12

let new_fid = Fid.next

(** Checks if a atom is consistent with a state, ie if the atomic propotisions 
    of the state is equal to the atomic propositions of the atom. *)
let dkey = Caret_option.register_category "formula_utils:atoms"
let dkey_consist = Caret_option.register_category "formula_utils_cons"

let dkey_next = Caret_option.register_category "formula_utils:nextReq"
let dkey_sid_eff = Caret_option.register_category "formula_utils:noSideEffect"
let dkey_z3 = Caret_option.register_category "formula_utils:z3"

(** 0. Formula printer *)

let pp_print fmt form = 
  
   let printOpKind = function
    | General -> "N "
    | Abstract -> "A "
    | Past -> "P "
  in
  let printInfo = function
    | ICall (Some s) -> "Call_" ^ s 
    | ICall _ -> "Call"
    | IRet (Some s) -> "Ret_" ^ s
    | IRet _ -> "Ret"
    |Caretast.IInt  -> "Int"
  in
  let rec printer fmt = 
    function
    | CNext (op,f) -> 
      Format.fprintf  fmt
        "X%s (%a)"
        (printOpKind op)
        printer f

    | CUntil  (op, f1 ,f2) -> 
      Format.fprintf  fmt
        "(%a) U%s (%a)"
        printer f1
        (printOpKind op)
        printer f2

    | CFatally (op,f) -> 
      Format.fprintf  fmt
        "F%s (%a)" 
        (printOpKind op) 
        printer f

    | CGlobally(op,f) ->
      Format.fprintf  fmt
        "G%s (%a)" 
        (printOpKind op) 
        printer f

    | CNot f -> 
      Format.fprintf  fmt
        "NOT(%a)" 
        printer f

    | CAnd (f1 ,f2) ->
      Format.fprintf  fmt
        "(%a) & (%a)"
        printer f1
        printer f2

    | COr (f1, f2)-> 
      Format.fprintf  fmt
        "(%a) | (%a)"
        printer f1
        printer f2

    | CImplies (f1, f2)-> 
      Format.fprintf  fmt
        "(%a) => (%a)"
        printer f1
        printer f2

    | CIff (f1, f2)-> 
      Format.fprintf fmt
        "(%a) <=> (%a)"
        printer f1
        printer f2

    | CTrue -> 
      Format.fprintf  fmt
        "TRUE"
    | CFalse -> 
      Format.fprintf  fmt
        "FALSE"
    | CProp (_,str) ->
      Format.fprintf  fmt
        "%s" str

    | CInfo i -> 
      Format.fprintf  fmt
        "%s" (printInfo i)

  in printer fmt form

(** 1. Predicate to smt solver z3 *)

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
	    lvars := Logic_var.Set.add lv !lvars; DoChildren
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
      
(** 2. CaFE formula utils *)

let mkIdForm f = 
  {
    f_id = new_fid ();
    form = f
  }

let getFormula id_form = id_form.form

let getFormId id_form = id_form.f_id

let findFormula form closure = 
(*  match form with
    CInfo _ -> assert false
  | _ -> *)
    try
      List.find 
	(fun f -> Caret_Formula.equal form f.form)
	closure
    with
      Not_found -> 
        Caret_option.fatal
           "Formula %a not found. Actual closure = %s"
           pp_print form
	  (
	  List.fold_left
	    (fun acc i_f -> acc ^ "\n" ^ (Caret_print.string_id_formula i_f)) "\n" closure
	  )
let isConsistent stmt ?(after = true) kf atom =
  (* let open Cil_types in *)
  let eval_to_bool = 
    let open Property_status in (* A module from the plugin Value *)
    function
    | True | Dont_know -> true 
    | False_if_reachable | False_and_reachable  -> false
  in

  let state = 
    let is_instr = 
      match stmt.Cil_types.skind with Cil_types.Instr _  -> true | _ -> false in
    
    if is_instr
    then
      try 
	let res_hashtbl = 
	  Extlib.the (Db.Value.get_stmt_state_callstack ~after stmt)
	in

	let res_state = 
	  Value_types.Callstack.Hashtbl.fold
	    (fun _ state acc -> 
	      match acc with 
		None -> Some state
	      | Some acc -> Some (Cvalue.Model.join acc state)
	    )
	    res_hashtbl
	    None
	in
	match res_state with
	  None -> Db.Value.get_stmt_state (List.hd stmt.Cil_types.succs)
	| Some s -> s
      with
      | Invalid_argument s -> 
	assert (s = "Extlib.the");
	Db.Value.get_stmt_state 
	  (match stmt.Cil_types.succs with [] -> stmt | hd :: _-> hd)
	  
    else
      (* We can here make a join of all the successors *)
      let res = 
	List.fold_left
	  (fun acc stmt -> 
	    let state = (Db.Value.get_stmt_state stmt) in
	    match acc with 
	      None -> Some state
	    | Some s -> Some (Cvalue.Model.join s state)
	  )
	  None
	  stmt.Cil_types.succs
      in
      match res with 
	None -> Db.Value.get_stmt_state stmt (* stmt.succs = [] *)
      | Some s -> s
  in
  (*let pre_states = 
    if stmt.preds = []
    then [Db.Value.get_initial_state kf]
    else
    List.fold_left
      (fun acc stmt -> 
        (Db.Value.get_stmt_state stmt)::acc)
      []
      stmt.preds
  in*)

  let eval_pred state pred = 
    
    !Db.Value.Logic.eval_predicate 
      (Db.Value.get_initial_state kf) 
      state 
      pred
  in

  let annot_pred = 
      List.fold_left
	(fun (acc:Cil_types.predicate) annot ->
	  match annot.Cil_types.annot_content with
	    Cil_types.AInvariant (_,_,pred) -> 
	      let () = 
		Caret_option.debug ~dkey:dkey_consist ~level:3
		  "Is annotation %a true ?"
		  Printer.pp_predicate pred in

	      let status = Property_status.get 
		(Property.ip_of_code_annot_single kf stmt annot) 
	      in 
	      let is_true () = 
		  begin 
		    match status with
		      Property_status.Best (Property_status.True,_) -> 
			let () = 
			  Caret_option.debug ~dkey:dkey_consist ~level:4
			    "Yes !" in true
		    | Property_status.Best _ -> 
		  let () = 
		    Caret_option.debug ~dkey:dkey_consist ~level:4
		      "No !" in false
	      | Property_status.Never_tried -> 
		Caret_option.debug ~dkey:dkey_consist ~level:4
		  "Never tried to prove it"; false
	      | Property_status.Inconsistent _ -> 
		Caret_option.debug ~dkey:dkey_consist ~level:4
		  "Inconsistent"; false
	      end 
	      in
	      if Caret_option.Assert_annot.get () || is_true () then 
		let () = 
		  Caret_option.debug ~dkey:dkey_consist ~level:4
		    "True or asserted"
		in 
		if acc.Cil_types.pred_content = Cil_types.Ptrue 
		then pred
		else Logic_const.unamed (Cil_types.Pand (acc,pred)) 
	      else	
		let () = 
		  Caret_option.debug ~dkey:dkey_consist ~level:4
		    "False"
		in 
		acc
	      
	  | _ -> acc
	)
	(Logic_const.unamed Cil_types.Ptrue)
	(Annotations.code_annot stmt)
  in
  let rec pred_of_form f =
    match f with
      CProp (pred,_) -> pred.Cil_types.ip_content
    | CNot p -> Logic_const.unamed (Cil_types.Pnot (pred_of_form p))
    | CTrue ->  Logic_const.unamed Cil_types.Ptrue
    | CFalse ->   Logic_const.unamed Cil_types.Pfalse
    | _ -> Logic_const.unamed Cil_types.Ptrue
  in 
  let pred_of_atom_and_asserts = 
    Id_Formula.Set.fold
      (fun form acc -> 
	Logic_const.unamed
	  (Cil_types.Pand(
	     acc,
	     (pred_of_form form.form))
	  )
      )
      (atomicProps atom)
      annot_pred
      
  in
  let res = 
    eval_to_bool (eval_pred state pred_of_atom_and_asserts)
    
  in
  let () = 
    Caret_option.debug ~dkey:dkey_consist ~level:2
      "Is %a possible ? Value says %b" 
      Printer.pp_predicate pred_of_atom_and_asserts 
      res in 

  if not res then false 
  else if annot_pred.Cil_types.pred_content = Cil_types.Ptrue
  then true
  else (** Checks if the atom /\ the annotation is satisfiable *)
    match z3_answer pred_of_atom_and_asserts with
    | Sat | Unknown -> true
    | Unsat -> false
  
let gen_next_hashtbl:(bool Atom.Hashtbl.t) Atom.Hashtbl.t = 
  Atom.Hashtbl.create 42

let abs_next_hashtbl:(bool Atom.Hashtbl.t) Atom.Hashtbl.t = 
  Atom.Hashtbl.create 42

let nextReq info closure atom1 atom2 = 

  let nextReqTest info closure atom1 atom2 = 
    
    let testNext atom1 atom2 next =
      let n_form = (getFormula next) in
      
      match n_form with
	CNext(i,prop) -> 
	  if i <> info then true 
	  else
	    if (formInAtom n_form atom1) 
	    then (formInAtom prop atom2)
	    else not (formInAtom prop atom2)
      | _ -> true
    in 
    List.for_all
      (testNext 
	 atom1
	 atom2)
      closure
  in
  
  let res_hshtbl = match info with
    | General -> gen_next_hashtbl
    | Abstract -> abs_next_hashtbl
    | Past -> assert false 
  in
  
  let a2_tbl = 
    try 
      Atom.Hashtbl.find
        res_hshtbl
	atom1
    with
      Not_found ->
	let () = 
	  Caret_option.debug ~dkey:dkey_next
	    "First time we see %s"
	    (Caret_print.string_atom atom1)

	in
        let new_tbl = Atom.Hashtbl.create 42
	  in
	  Atom.Hashtbl.add 
	    res_hshtbl
	    atom1
	    new_tbl;
	  new_tbl
  in
  try
    let res = 
      Atom.Hashtbl.find 
	a2_tbl
	atom2
    in
    let () = 
      Caret_option.debug ~dkey:dkey_next
	"%s -> %s -> %b"
	
	(Caret_print.string_atom atom1)
	
	(Caret_print.string_atom atom2)
	res
    in
    res
  with
    Not_found -> 
      	let () = 
	  Caret_option.debug ~dkey:dkey_next
	    "First time we see %s after %s"
	    (Caret_print.string_atom atom2)
	    (Caret_print.string_atom atom1)

	in
      let res = nextReqTest info closure atom1 atom2
      in
      Atom.Hashtbl.add
        a2_tbl
	atom2
	res;
      Caret_option.debug ~dkey:dkey_next 
	"%s -> %s -> %b"
	
	(Caret_print.string_atom atom1)
	
	(Caret_print.string_atom atom2)
	res;
      res
	
let absNextReq closure atom1 atom2 = 

  nextReq Abstract closure atom1 atom2
    
let glNextReq closure atom1 atom2 = 
  
  nextReq General closure atom1 atom2

let no_side_effect_hshtbl:(bool Atom.Hashtbl.t) Atom.Hashtbl.t = 
  Atom.Hashtbl.create 42

exception VarInPred

let filter_atom_without_v atom v = 
  
  let pred_vis = 
    object
      inherit Visitor.frama_c_inplace
      method! vlogic_var_use lv = 
	match lv.Cil_types.lv_origin with
	  Some var -> 
	    if Varinfo.equal v var
	    then raise VarInPred
	    else DoChildren
	| None -> DoChildren
    end
  in
  
  Id_Formula.Set.filter
    (fun form -> 
      match (getFormula form) with
	CProp (p,_) -> 
	  begin
	    try 
	      ignore 
		(Cil.visitCilPredicate 
		   (pred_vis :> Cil.cilVisitor) 
		   p.Cil_types.ip_content);
	      true
	    with
	      VarInPred -> false
	  end
      | _ -> false
    )
    (getPropsFromAtom atom)
  

let noSideEffectNextReq ?var atom1 atom2 = 
  
  let a2_tbl = 
    try 
      Atom.Hashtbl.find
        no_side_effect_hshtbl
	atom1
    with
      Not_found -> 
	let () = 
	  Caret_option.debug ~dkey:dkey_sid_eff 
	    "First time we see %s"
	    (Caret_print.string_atom atom1)
	    
	in
	let new_tbl = Atom.Hashtbl.create 42
	in
	Atom.Hashtbl.add 
	  no_side_effect_hshtbl
	  atom1
	  new_tbl;
	new_tbl
  in
  try
    let res = Atom.Hashtbl.find 
      a2_tbl
      atom2
    in
    let () = 
      Caret_option.debug ~dkey:dkey_sid_eff
	"%s -> %s -> %b"
	
	(Caret_print.string_atom atom1)
	
	(Caret_print.string_atom atom2)
	res
    in
    res
  with
    Not_found -> 
      let res = 
	match var with 
	  None -> 
	    Id_Formula.Set.equal
	      (atomicProps atom1)
	      (atomicProps atom2)
	| Some v -> 
	    
	  let aprops1 = filter_atom_without_v atom1 v
	  in
	  let aprops2 = filter_atom_without_v atom2 v
	  in   
	  Id_Formula.Set.equal aprops1 aprops2
      in
      
      let () = (* Adding the results iff we didn't had to check for a 
		  variable *)
	if var = None then
	let () = 
	  Caret_option.debug ~dkey:dkey_sid_eff
	    "%s -> %s -> %b"
	    
	    (Caret_print.string_atom atom1)
	    
	    (Caret_print.string_atom atom2)
	    res
	in
	Atom.Hashtbl.add 
          a2_tbl 
	  atom2 
	  res;
      in
      res
	
let (caller_hshtbl:(Id_Formula.Set.t) Atom.Hashtbl.t) = Atom.Hashtbl.create 42
    
let callerFormulas atom = 
  try 
    Atom.Hashtbl.find 
      caller_hshtbl
      atom
  with
    Not_found -> 
      let res = 
	Id_Formula.Set.filter 
	  ( fun f -> 
	    let form = getFormula f in
	    match form with CNext (Past , _) -> true | _ -> false )

	  (getPropsFromAtom atom)
      in
      Atom.Hashtbl.add 
	caller_hshtbl
	atom
	res;
      res

(** Functions treating the CaRet formula  *)
let normalizeFormula formula = 
  let rec removeUndefOp = function
    (* F a = True U a *)
    | CFatally (op, f) -> (CUntil(op, CTrue, removeUndefOp f)) 
    (* G a = Not (F (Not a)) *)
    | CNot (CGlobally (op, f)) -> removeUndefOp (CFatally (op,(CNot f)))
    | CGlobally (op, f) -> removeUndefOp (CNot (CFatally (op,(CNot f)))) 
    | CNext (op,f) -> CNext (op,removeUndefOp f)
    | CUntil (op, f1, f2) -> CUntil (op, removeUndefOp f1, removeUndefOp f2)
    | CNot CTrue -> CFalse
    | CNot CFalse -> CTrue
    | CNot (CNot f) -> (removeUndefOp f)
    | CNot f -> CNot ( removeUndefOp f )
    | COr (f1, f2) -> COr (removeUndefOp f1, removeUndefOp f2) 
    | CAnd (f1, f2) -> CAnd (removeUndefOp f1, removeUndefOp f2)
    | CImplies (f1, f2) -> CImplies (removeUndefOp f1, removeUndefOp f2)
    | CIff (f1,f2) -> CIff (removeUndefOp f1, removeUndefOp f2) 
    | CProp _ | CInfo _ | CTrue | CFalse as f -> f
  in removeUndefOp formula (* Todo : more simplification *)

let rec size_form form = 
  match form with
    CNext (_, f) |CFatally (_, f) |CGlobally (_, f)  -> 1 + size_form f
  | CUntil (_, f1, f2)  
  |COr (f1, f2) 
  |CAnd (f1, f2) 
  |CImplies (f1, f2) 
  |CIff (f1,f2) -> 1 + (size_form f1) + (size_form f2)
  |CNot f -> size_form f
  |CProp _ |CInfo _ |CFalse |CTrue -> 1

(*let mkAtomsWithoutClosure formula = 
  (* We treat only non-negative formulas, we add them later. *)
  let formula = match formula with CNot f -> f | _ -> formula in 

  let raw_atoms = [Id_Formula.Set.empty]
  in
  let closure = ref []
  in
  (* todo : add hashtbl string -> id_form to avoid double formulas *)
  let addWithNeg f atoms = 
    List.fold_left
	(fun acc atom -> 
	    (*match flag with
	      Some true -> 
		(Id_Formula.Set.add (mkIdForm f) atom) :: acc

	    | Some false -> 
	      (Id_Formula.Set.add (mkIdForm (CNot f)) atom) :: acc
	    
	    | None ->*) 
	      (Id_Formula.Set.add (mkIdForm f) atom) 
	      ::
		(Id_Formula.Set.add (mkIdForm (CNot f)) atom)
	      ::
		acc
	)
      []
      atoms
  in

  let dfsFormula form atoms = match form with
      CTrue | (CNot CFalse) -> acc

    | CFalse | (CNot CTrue) -> []

    | CProp _ -> addWithNeg form atoms
	    
    | CNext f -> addWithNeg form (dfsFormula f atoms)

    | COr (f1, f2) -> 
      let new_atoms = 
	(dfsFormula f1 (dfsFormula atoms f2))
      in
      List.map
	(fun atom -> 
	  Id_Formula.Set.exists
	    ( *)
  

let closure formula = 

  (* We treat only non-negative formulas, we add them later. *)
  let formula = match formula with CNot f -> f | _ -> formula in 

  Caret_option.debug ~dkey "Computing the closure";

  let rec __closure acc formula =
    let forms = match formula with
	CNot f -> [f;formula]
      | _ -> [formula;CNot(formula)]
    in
  let () = Caret_option.feedback "Formula : %a"
      pp_print formula in
    if List.exists 
      (fun form -> List.exists
	(fun form2 -> Caret_Formula.equal form form2) forms) acc
    then 
      let () = Caret_option.feedback "Formula already in the closure" in acc
    else
      let () = Caret_option.feedback "Formula not in the closure" in
      begin 
	match formula with 
	  CNext (_ , f) -> 
	    __closure 
	      (formula :: acc) 
	      f
	      
	| CUntil (op, f1, f2) -> 
	  __closure 
	    (__closure 
	       (formula :: (CNext (op, formula)) ::acc) 
	       f1
	    )
	    f2
	    
      (* At this moment, we don't have any "negative formula". 
	 We will add it later for all subformulas. *)	
	|CNot f -> __closure acc f 
	  
	|COr (f1, f2) |CAnd (f1,f2) |CImplies (f1, f2) ->
	  __closure
	    (__closure (formula :: acc) f1)
	    f2
	    
    (* Todo : delete iff in normalizeFormula*)
	|CIff (f1,f2) -> 
	  __closure acc (CAnd ((CImplies (f1,f2)), (CImplies (f2,f1))))
	    
	| CTrue | CFalse | CInfo _ | CProp _ -> formula::acc	
	  
	|CFatally _ -> 
	  Caret_option.debug ~dkey ~level:1 
	    "Formula badly normalized, %a contains Fatally."
                pp_print formula; 
	  Caret_option.fatal ~dkey
	    "Closure failed : \"Fatally\" found."
	    
	|CGlobally _ -> 
	  Caret_option.debug ~dkey ~level:1 
	    "Formula badly normalized, %a contains Globally."
	    pp_print formula;
	  Caret_option.fatal ~dkey
	    "Closure failed : \"Globally\" found." 
      end  
   (*in
      TODO : Optimize by filtering doubles directly in __closure if possible 
  let rec removeDouble l =
    match l with
      []-> []
    | h::t -> if List.mem h t then removeDouble t else (h :: removeDouble t) *)

  in  
  let pre_closure = 
    List.fold_left 
      (fun acc form -> 
	let rec check_form acc form = 
	  match form with 
	    CTrue | CFalse | CNot CTrue | CNot CFalse -> 
	      CNot CTrue :: CTrue :: CNot CFalse :: CFalse :: acc
	  (*| CInfo _ -> form :: CNot form :: acc*)
	  | CNot CNot f -> check_form acc f
	  | CNot f -> f :: CNot f :: acc 
	  | _ -> form :: CNot form :: acc
	in
	check_form acc form
      )
      []
      (__closure [] formula)
    
  in
  (*
  Id_Formula.Set.of_list*)

(** To compute atoms efficiently, we need to sort the closure list by comparing the size of each formula.*)
  let closure = 
    
    let unsorted_closure = 
      List.map 
	(function elt -> ((mkIdForm elt),(size_form elt)))
	pre_closure
    in
    let compare (_ , s1) (_ , s2) = s2 - s1
    in
    List.fast_sort compare unsorted_closure
  in
  (* "closure" is now the list sorted as the smallest elements are at the 
     beginning. *)
  fst (List.split closure)
    
(* TODO : se renseigner sur les monades de liste pour générer l'ensemble des parties de la liste verifiant les propriétés de l'atome.  *)

(** Be careful : if you want this function to work, the closure list must be sorted from the smallest element to the biggest, as done in the actual closure function. *)
let mkAtoms closure atom_hashtbl = 

  let atomic_list,next_list,call_int_ret,other_form = 
    List.fold_left
      (fun (acc_at, acc_n, acc_info, acc_other) i_form-> 
	let form = getFormula i_form in
	  match form with
	  | CProp _ ->
	    ((i_form :: acc_at), 
	     acc_n, 
	     acc_info, 
	     acc_other)
	        
	  | CNext _ -> 
	    (acc_at, 
	     (form :: acc_n), 
	     acc_info, 
	     acc_other)

(*	  | CNot (CNext _ as f) -> 
	    
	    (acc_at, 
	     acc_no_at, 
	     (f :: acc_n), 
	     acc_info, 
	     acc_other)
*)
	  | CInfo _ -> 
	    (acc_at, 
	     acc_n, 
	     (i_form :: acc_info), 
	     acc_other)
	      
	  | CNot _ | CTrue | CFalse -> 
	    (acc_at, 
	     acc_n, 
	     acc_info, 
	     acc_other)
	  | _ -> 
	    (acc_at, 
	     acc_n, 
	     acc_info, 
	     (i_form :: acc_other))
      )
      ([],[],[],[])
      closure
  (* 
  in
  let atomic_list,other_forms = 
    List.partition 
      (fun id_form -> 
	let form = getFormula id_form in
	match form with
(*	  CInfo _ | CNot _ | CTrue | CFalse -> false 
	(* In the closure, there is Not formulas and CInfos : 
	   we don't want them for atoms right now. *)
	|  _ -> size_form form = 1 *)
	  | CProp _ -> true
	  | _ -> false
	) 
	closure*)
  in
  let () = 
    Caret_option.debug 
    ~dkey 
    "atomic properties = %s end" 
    (List.fold_left 
       (fun a f -> a ^ (Caret_print.string_id_formula f)^"\n") 
       "" 
       atomic_list
       ) in 
  let () =
    Caret_option.debug 
      ~dkey 
      "Nexts : %s\nInfos : %s\nElse : %s"
      (List.fold_left
	 (fun acc f -> acc ^ Caret_print.string_formula f)
	 ""
	 next_list  
      )
      (
	List.fold_left
	  (fun acc f -> acc ^ Caret_print.string_id_formula f)
	  ""
	  call_int_ret
      )
      
      (
	List.fold_left
	  (fun acc f -> acc ^ Caret_print.string_id_formula f)
	  ""
	  other_form
      )
  in
  let addListsWithNeg big_l elt = 
    
   (* let pos_elt = match elt.form with
	CNot f -> f
      | _ as f -> f
    in
   *)
    let f = getFormula elt in
    (List.fold_left
       (fun acc set -> 	 
	 if formInRawAtom f set 
	   || formInRawAtom (CNot f) set
	  	 
	 then 
	   begin
	     Caret_option.debug
	       ~dkey
	       "Formula %s already in \n%s"
	       (Caret_print.string_id_formula elt)
	       (Caret_print.string_raw_atom set);
	     set :: acc
	   end
	 else
	   begin
	     Caret_option.debug
	       ~dkey
	       "Formula %s not in \n%s"
	       (Caret_print.string_id_formula elt)
	       (Caret_print.string_raw_atom set);

	     (Id_Formula.Set.add 
		elt 
		set) 
	     :: (Id_Formula.Set.add 
		   (findFormula (CNot (getFormula elt)) closure) 
		   set) 
	     :: acc
	   end
       )
       []
       big_l)
  in
  
  let rec list_parts acc l = match l with
      [] -> acc
    | hd::tl ->
      list_parts  (addListsWithNeg acc hd) tl 
  in

  let atomic_parts = 

      (list_parts [Id_Formula.Set.empty] atomic_list) 

      (* try List.tl (list_parts [[]] atomic_list) with _ -> [[]] *)

  in

  (* We have a list with sets of properties. We call now a SMT solver in 
     order to check if the future atom is possible.  *)
  let () = 
    Caret_option.debug ~dkey ~level:3 "Testing atom consistency" in

  let atomic_parts = 
    if Caret_option.Atom_simp.get ()
    then
    List.filter
      (fun a -> 
	try Smt_solver.cvcTest a
	with | _ -> let () = Caret_option.feedback ~dkey "cvc failed" in true)
      atomic_parts
  else atomic_parts
  in
  if atomic_parts = []
  then
    raise Unsatisfiable_formula;

  Caret_option.debug
    ~dkey
    "atomic parts  =\n %s"
    (List.fold_left
       (fun a elt -> a ^ "[ "^(Caret_print.string_raw_atom elt)^ "]\n")  
       "" 
       atomic_parts

    );
 
 (* let next_list,other_forms =
    List.fold_left
      (fun (acc_n,acc_oth) id_form -> 
	let form = getFormula id_form in
	match form with
	| CNext _ -> (form :: acc_n), acc_oth
	| CNot (CNext _ as f) -> (f :: acc_n),acc_oth
	| _ -> acc_n , (form::acc_oth))
      ([],[])
      other_forms
  
  in *)
  let atomic_parts = 

    let testIfNoNeg next atom = 

	  match next with
	    CNext (op,(CNot f)) -> 
	    not (formInRawAtom (CNext  (op,f)) atom ||
		   formInRawAtom (CNot next) atom)
	  | CNext (op,f) ->
	      not (formInRawAtom (CNext (op,CNot f)) atom ||
		     formInRawAtom (CNot next) atom)
          
	  | CNot (CNext (op,CNot f)) -> 
	    not (formInRawAtom (CNot (CNext (op,f))) atom || 
		   formInRawAtom ((CNext (op,CNot f))) atom)

	  | CNot ( CNext (op,f)) ->
	    not (formInRawAtom (CNext (op,f)) atom || 
		   formInRawAtom (CNot (CNext (op,CNot f))) atom)
	      
	  | _ -> assert false

    in
    List.fold_left 
      (fun acc elt -> 
	List.fold_left
	  (fun acc2 set -> 
	    let genAtom elt atom_acc = 
	      if testIfNoNeg elt atom_acc
	      then
		let id_form = 
		  try
		    findFormula elt closure
		  with
		    Not_found -> 
		      mkIdForm elt (* Maybe a bug, forbids invariants : 
				      - all "next"
				      id_formulas must be in the closure
				      - there is no two identical id_formula
				      with the same id*)
		in
		Some
		  (Id_Formula.Set.add 
		     id_form 
		     atom_acc)
	      else
		None
	    in
	    match (genAtom elt set),(genAtom (CNot elt) set) with
	      None,None -> acc2
	    | None, Some a | Some a, None -> a::acc2
	    | Some a, Some b -> a::b::acc2
	  
	  )
	  [] 
	  acc
      
      ) 
      atomic_parts
      next_list
      
  in
  Caret_option.debug
    ~dkey
    "atomic parts with next =\n %s"
    (List.fold_left 
       (fun a l -> a ^ (Caret_print.string_raw_atom l)^ "\n") 
       "" 
       atomic_parts
    );
(*
  let pre_atoms = 
    (* We now add the call / ret /int information, if there is *)
    let pure_info,advanced_info = 
      List.partition 
	(fun info -> 
	  match info with
	    ICall None | IRet None | IInt -> true
	  | _ -> false)
	call_int_ret
    in
    let call_atoms,ret_atoms,int_atoms = 
      List.fold_left 
	(fun acc set -> )
*)    
  let pre_atoms = 

    (* We create the base for our atoms. For
       each set we created, we check if a property
       not(ret), not(call) or not (int) would make
       an atom inconsistent with itself. *)

    (*let spotNextPattern op_k set_form = 
      Id_Formula.Set.exists
	(fun id_form -> 
	  match id_form.form with
	  | CNext (op,_) -> op = op_k 
	  | _ -> false)
	set_form
    in*)
    let advanced_info = 
      List.filter 
	(fun info -> 
	  match (getFormula info) with
	    (CInfo ICall None) | (CInfo IRet None) | (CInfo IInt) -> false
	  | _ -> true)
	call_int_ret
    in
    List.fold_left 
      (fun acc set -> 
	(*if set <> Id_Formula.Set.empty 
	then 
	  let pre_list = 
	    if 
	      (formInRawAtom (CNot (CInfo (ICall None))) set)
		
	    then acc
	    else ref(mkAtom (ICall None) set) :: acc
	  in
	  let pre_list = 
	    if 
	      (formInRawAtom (CNot(CInfo (IRet None))) set)
	    then pre_list
	    else ref(mkAtom ARet set) :: pre_list
	  in
	  if 
	    (formInRawAtom (CNot(CInfo IInt)) set)
	  then pre_list
	  else ref(mkAtom AInt set) :: pre_list
	  else acc*)

	List.fold_left 
	  (fun acc2 a_i -> 
	    match (getFormula a_i) with
	      CInfo info -> 
		  ref
		    (mkAtom 
		       info
		       set) :: acc2
	    | _ -> assert false)
	  (ref (mkAtom IInt set)::
	  ref (mkAtom (IRet None) set)::
	  ref (mkAtom (ICall None) set)::
	  acc)
	  
	  
	  advanced_info      

	  (*
	ref(mkAtom IInt set) ::
	  ref(mkAtom (IRet None) set) ::
	  ref(mkAtom (ICall None) set) :: 
	  acc
	  *) 

      )
      []
      atomic_parts
  in
  Caret_option.debug
    ~dkey
    "pre atoms =\n %s"
    (List.fold_left 
       (fun a at -> a ^ (Caret_print.string_atom !at)^ "\n") 
       "" 
       pre_atoms
    );
  let testPossible atom f = 
    let form = getFormula f in
      (*let infoToAKind = function
	| ICall _ -> ACall
	| IRet _ -> ARet
	| IInt -> AInt
      in*)
    (*let rec notTest atom form = match form with 
	CNot f -> not(formInAtom f atom)
      | CInfo i -> (getAtomKind atom) <> i 
      (* | CInfo IRet -> (getAtomKind atom) <> IRet
	| CInfo IInt -> (getAtomKind atom) <> IInt  *)
      | CTrue -> false
      | CFalse -> true
      | CImplies (f1,f2) -> (formInAtom f1 atom) && not(formInAtom f2 atom)
	
      |_ -> not(formInAtom (CNot form) atom)
    *)
      let lastTests atom form = match form with
	| CInfo i ->  
	  begin
	    let () = Caret_option.debug ~dkey
	      "Can %a be in %s ?"
	      pp_print form
	      (Caret_print.string_atom atom)
	    in
	    match i with
	      ICall (Some _) | IRet (Some _) -> 
		(getAtomKind atom) = i
		
	    | ICall None -> isACall atom
	    | IInt -> isAInt atom
	    | IRet None -> isARet atom 
	  end
	| COr (f1, f2) -> (formInAtom f1 atom) || (formInAtom f2 atom)
	| CAnd (f1, f2) -> (formInAtom f1 atom) && (formInAtom f2 atom)
	| CUntil (op, f1, f2) ->
          (*let () = 
            Caret_option.debug
	      ~dkey
              "Until detected : %a."
              pp_print form in
	    *)
          begin
	    match f1,f2 with 
	      
	    | _,CTrue -> true
	    | CFalse,_ -> false
	    | _, _ -> 
	      	      
	      (formInAtom f2 atom) || 
		((formInAtom f1 atom) 
		 && (formInAtom (CNext(op, CUntil(op, f1, f2))) atom))
	  end
	| CNot _ -> assert false 
	| CImplies (f1,f2) -> ((formInAtom f2 atom) || not(formInAtom f1 atom))
	| CFalse -> false
	| CTrue -> true
	| _ -> false
      in
      not(formInAtom form atom) && (lastTests atom form) 
  in

  let addIfPossible form atom = 
    if testPossible !atom form
    then 
      begin (*
	Caret_option.debug
	  ~dkey
	  "Formula %a accepted in atom %s "
	  pp_print (getFormula form)
	  (Caret_print.string_atom !atom);
      *)addForm form !atom 
      end
    else 
      begin
      (*Caret_option.debug
	~dkey
	"Formula %s not accepted in atom \n:%s "
	pp_print (getFormula form)
	(Caret_print.string_atom !atom);
	*)match (getFormula form) with

	  CNot f -> addForm (findFormula f closure) !atom
	| _ -> 
	  addForm (findFormula (CNot (getFormula form)) closure) !atom

      end
  in

  let no_no = 
    List.filter
      (fun id_form -> 
	match getFormula id_form with
	  CNot _  -> false
	| _ -> true ) 
      (call_int_ret@other_form)

  in

  let () = 
    List.iter
      (fun atom -> 
	List.iter 
	  (fun form -> addIfPossible form atom)
	  no_no 
      )
      pre_atoms
  in
  List.iter
    (fun atom -> 
      let old_bind = 
	  try 
	    Hashtbl.find atom_hashtbl (getAtomKind !atom)
	  with
	    Not_found -> 
	      Atom.Set.empty
		
      in
      Hashtbl.replace 
	atom_hashtbl 
	(getAtomKind !atom) 
	(Atom.Set.add !atom old_bind)
	
    )
    pre_atoms
    
  
(*  List.fold_left 
    (fun acc atom -> Atom.Set.add !atom acc)
    Atom.Set.empty
    pre_atoms
*)

let string_spurious () = 
  Cil_datatype.Stmt.Hashtbl.fold
    (fun stmt form_set acc -> 
      acc ^ "On statement " ^ (Caret_print.string_stmt stmt) 
      ^ " of " ^ (Kernel_function.get_name (Kernel_function.find_englobing_kf stmt))
      ^ ", there is spurious formulas :\n" ^ 
	(Caret_print.string_raw_atom form_set))
    spurious_stmt_hashtbl 
    ""
