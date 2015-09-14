open Caretast  
open Formula_datatype
open Atoms
open Atoms_utils
open Rsmast

open Type_RState
open Type_Box
open Type_Rsm_module
open Ext_state

exception Inconsistent_atom of atom_kind
exception Found of r_module 
exception Deleted

module Sid = State_builder.SharedCounter(struct let name = "sid_counter" end)
module Mid = State_builder.SharedCounter(struct let name = "mid_counter" end)
module Bid = State_builder.SharedCounter(struct let name = "bid_counter" end)
module Rid = State_builder.SharedCounter(struct let name = "rsm_cpt" end)

let new_sid = Sid.next
let new_mid = Mid.next
let new_bid = Bid.next
let new_rid = Rid.next

let dkey = Caret_option.register_category "rsm:utils" 
let dkey_simp = Caret_option.register_category "rsm:simpl"
let dkey_accept = Caret_option.register_category "rsm:accept"

(* Imported functions from Caret_print *)
let string_stmt stmt =
 

  let orig_str = 
    String.trim
      (Format.fprintf 
	 Format.str_formatter 
	 "@[%a@]" 
	 Printer.pp_stmt 
	 stmt;
       Format.flush_str_formatter ()
      )
  in (*
  if String.length orig_str > 15
  then
   String.sub orig_str 0 15
  else*)
    orig_str
  ^(string_of_int stmt.Cil_types.sid)
 
let simple_state (state:state) = 

  ("\"" ^ (string_stmt state.s_stmt) ^ "_st_" ^ 
      (string_of_int state.s_id) ^ ": " ^ state.s_name ^ "\"")

(*
let simple_state_set set =  
  RState.Set.fold(
    fun st acc -> "\n" ^ (simple_state st) ^ acc
  )
    set
    "\n"
let string_box box = 
  
  "Box " ^ box.b_name ^ "_" ^ (string_of_int box.b_id)
 
  ^ "\n\nEntries :\n" 
  ^ RState.Map.fold 
    (fun call ent acc -> 
      acc ^ (simple_state call) 
      ^ "->" ^ (simple_state_set ent) ^ "\n")
    box.b_entries
    ""
  ^ "\nExits :\n"
  ^ RState.Map.fold 
    (fun ext ret acc  -> 
      acc ^ (simple_state ext) 
      ^ "->" ^ (simple_state_set ret) ^ "\n")
    box.b_exits
    ""
*)


(** 2. Modules management  *)
    
let mkModule 
    nam 
    ?(st = RState.Set.empty) 
    ?(in_st = RState.Set.empty) 
    ?(out_st = RState.Set.empty) 
    is_fun = 
  let n = new_mid () in 
  {
    mod_name = nam ;
    is_func = is_fun;
    states = st ;
    entries = in_st ;
    exits = out_st ;
    mid = n ;
    box_repres = Box.Set.empty;
    box_belong = Box.Set.empty;
  }
  
let mkBox name r_mod_repr r_mod_bel atom tag = 
  let box = {

    b_name = name;
    r_mod_repres = r_mod_repr;
    r_mod_belong = r_mod_bel;
    b_id = new_bid ();
    box_atom = atom;
    box_tag = tag;
    b_entries = RState.Map.empty;
    b_exits = RState.Map.empty  
          
  }
  in
  r_mod_repr.box_repres <- Box.Set.add box r_mod_repr.box_repres;
  r_mod_bel.box_belong <- Box.Set.add box r_mod_bel.box_belong;
  box

let plugEntryBox box scall sentry = 
  
  let old_bind = 
    try 
      RState.Map.find scall box.b_entries
    with
      Not_found -> RState.Set.empty
  in
  box.b_entries <- 
    (RState.Map.add
       scall 
       (RState.Set.add sentry old_bind) 
       box.b_entries);

  scall.call <- 
    match  scall.call with
	None -> Some (box,RState.Set.singleton sentry)
      | Some (box,set) -> Some (box, RState.Set.add sentry set)

let plugExitBox box sexit snext = 
 
    let old_bind = 
      try 
	RState.Map.find sexit box.b_exits
      with
	Not_found -> RState.Set.empty
    in
    
    box.b_exits <- 
      (RState.Map.add sexit (RState.Set.add snext old_bind) box.b_exits);
    snext.return <-
      
      match  snext.return with
	None -> Some (box,RState.Set.singleton sexit)
      | Some (box,set) -> Some (box, RState.Set.add snext set)

let isMainMod r_mod = 
  
  r_mod.is_func.Cil_types.vorig_name = "main"

let getMainMod rsm = 

  try
    let () = Rsm_module.Set.iter
    (fun r_mod -> if isMainMod r_mod then raise (Found r_mod))
    rsm.rsm_mod
    in
    raise Not_found
  with
    Found r -> r
      
(** 3. RState management *)

let mkRState name ?(acpt = Id_Formula.Set.empty) stmt atom info r_mod = 

    let n = new_sid () 
    in
      {
	s_name = name ;
	s_accept = acpt ;
	call = None ;     (* To change those, you need to *)
	return = None ;   (* use the plug functions *)
	s_stmt = stmt;
	s_atom = atom;
	s_info = info;
	s_id = n ;
	s_mod = r_mod;      
	s_succs = RState.Set.empty;
	s_preds = RState.Set.empty;
	summary_succs = RState.Set.empty;
	summary_preds = RState.Set.empty;
    } 

  
let mkCall name ?(acpt = Id_Formula.Set.empty) stmt box entry r_mod = 
  
    let st = 
      mkRState 
	name 
	~acpt  
	stmt
        box.box_atom
        (Tag box.box_tag) 
	r_mod
    in
    plugEntryBox box st entry;
    st

let mkReturn name ?(acpt = Id_Formula.Set.empty) stmt atom box ext r_mod = 

    let st = 
      mkRState 
	name 
	~acpt
	stmt 
        atom
	(Tag box.box_tag) 
	r_mod
    in 
    plugExitBox box ext st ;
    st


(** Returns [true] iff the state is an entry state *)
let isExit state = match state.s_info with Tag _ -> false | TagR -> true

let isCall state = state.call <> None

let isRet state = state.return <> None

(** Returns [true] iff the state is an entry state *)
let isEntry state = 
  RState.Set.is_empty state.s_preds
    && not(isRet state)

let getCalledFunc s = 
  match (s.call,s.return) with
    Some (b,_), _ | _, Some (b,_) -> b.r_mod_repres.is_func
  | _, _ ->  raise Not_found

let isStart state = 
  isMainMod state.s_mod 
  && state.s_info = Tag Inf 
  && isEntry state

let isDeleted state = state.s_id < 0

let deleteRState state = (* todo : delete in boxes or change id to -1 *)
  assert ((Caret_option.Simplify.get ()) <> 0);
  if isDeleted state then () else 
    let () = 
      let rmod = state.s_mod
      in
      let () =
	if isEntry state
	then
	  begin (* isEntry state *)
	    rmod.entries <- RState.Set.remove state rmod.entries;
      (*	List.iter
		(fun box -> 
	  RState.Map.iter 
		(fun call entry -> 
		if RState.equal entry state 
		then )
		box.b_entries)
		
		rmod.box_repres*)
	  end (* isEntry state *)
	else       
	  if isExit state
	  then
	    rmod.exits <- RState.Set.remove state rmod.exits
	  else 
	    if isCall state
	    then
	      begin
		let box = (fst(Extlib.the state.call))
		in
		
		box.b_entries <- RState.Map.remove state box.b_entries;
		
	      end
	    else 
	      if isRet state
	      then 
		begin
		  let box = (fst(Extlib.the state.return))
		  in
		  
		  box.b_exits <- RState.Map.remove state box.b_exits;
		  
		end
		  
      in
      
      state.call <- None;
      state.return <- None;
      
      rmod.states <- RState.Set.remove state rmod.states;
      
      let () = 
	RState.Set.iter
	  (fun pred -> pred.s_succs <- RState.Set.remove state pred.s_succs)
	  state.s_preds
      in
      RState.Set.iter
	(fun succ -> succ.s_preds <- RState.Set.remove state succ.s_preds)
	state.s_succs;
      
      state.s_succs <- RState.Set.empty;
      state.s_preds <- RState.Set.empty in
  (*state.s_stmt <- Cil.dummyStmt;*)
    state.s_name <- "DELETED" ^ state.s_name;
    state.s_id <- -1 * state.s_id
      
let addRState st ?(entry = false) ?(exits = false) r_mod = 

      if not(RState.Set.mem st r_mod.states) 
      then r_mod.states <- RState.Set.add st r_mod.states;
  
      if entry then r_mod.entries <- RState.Set.add st r_mod.entries
      else 
	if exits then r_mod.exits <- RState.Set.add st r_mod.exits;

      st.s_mod <- r_mod

let addRStates s_set r_mod = 
  RState.Set.iter
    (fun state -> addRState state r_mod)
    s_set

let addEntry state r_mod = addRState state ~entry:true r_mod

let addExit state r_mod = addRState state ~exits:true r_mod

let addEntries s_list r_mod = 
  List.iter
    (fun state -> addEntry state r_mod)
    s_list

let addExits s_list r_mod = 
  List.iter
    (fun state -> addExit state r_mod)
    s_list

let throughBox state box = 
  
  try 
    if isCall state
    then RState.Map.find state box.b_entries
    else 
      if isExit state
      then RState.Map.find state box.b_exits
      else assert false
  with Not_found -> RState.Set.empty

(** Transitions management *)

let mkTrans sta sto = 
  
  sta.s_succs <- RState.Set.add sto sta.s_succs;
  sto.s_preds <- RState.Set.add sta sto.s_preds

let mkSummaryTrans call ret = 

  let () = 
    if not (isCall call)
    then Caret_option.fatal "%s is not a call" call.s_name
    else 
      if not (isRet ret)
      then Caret_option.fatal "%s is not a return" ret.s_name
  in

  ret.summary_preds <- RState.Set.add call ret.summary_preds;
  call.summary_succs <- RState.Set.add ret call.summary_succs

(** Rsm management *)
let mkEmptyRsm nam = 
  {
    rsm_id = new_rid ();
    name = nam;
    rsm_mod = Rsm_module.Set.empty;
    start = RState.Set.empty;
    (*inf_states = [];*)
    until_set = Id_Formula.Set.empty;
  }

let addMod r_mod rsm = rsm.rsm_mod <- Rsm_module.Set.add r_mod rsm.rsm_mod

let setStart state rsm = 
  rsm.start <- RState.Set.add state rsm.start 

let generateBuchi closure rsm = 
  
  List.fold_left
    (fun acc id_form -> 
      match id_form.form with
      | CUntil(Abstract,_,_) 
      | CUntil(General,_,_) -> 
	Id_Formula.Set.add id_form acc
      | _ -> acc)
    rsm.until_set
    closure

let addBuchiToRStates rsm = 
  
  let addForm st id_form = 
    st.s_accept <- Id_Formula.Set.add id_form st.s_accept
  in
  Rsm_module.Set.iter 
    (fun r_mod -> 
      RState.Set.iter 
	(fun st -> 
	  if not(RState.Set.mem st r_mod.entries)
	  then
	    let st_info =  
	      if st.call <> None
	      then Tag ( fst (Extlib.the st.call)).box_tag
	      else 
		if st.return <> None
		then Tag ( fst (Extlib.the st.return)).box_tag
		else st.s_info
	    in
	    let checked_atom =  st.s_atom
	    in
	    
	    Id_Formula.Set.iter 
	      (fun id_form -> 
		let form = id_form.form in
		  match form with
		    CUntil(General,_,f2) -> 
		      if 
			(not(formInAtom form checked_atom) 
			|| (formInAtom f2 checked_atom))
		      then
			begin
			  Caret_option.debug ~dkey:dkey_accept
			    "State %s accepted ! %b -- %b"
			    (simple_state st)
			    (not(formInAtom form checked_atom))
			    (formInAtom f2 checked_atom);
			  addForm st id_form
			end
		      else
			Caret_option.debug ~dkey:dkey_accept
			  "State %s refused ! %b -- %b"
			  (simple_state st)
			  (not(formInAtom form checked_atom))
			  (formInAtom f2 checked_atom);
		  | CUntil (Abstract,_,f2) -> 
		    if 
		      (
			((*not(List.mem st r_mod.exits)
			 &&*)
			  (not(formInAtom form checked_atom) 
			|| (formInAtom f2 checked_atom)))
			 && (st_info = Tag Inf))
		    then
		      begin
			Caret_option.debug ~dkey:dkey_accept
			  "State %s accepted ! %b -- %b"
			  (simple_state st)
			  (not(formInAtom form checked_atom))
			  (formInAtom f2 checked_atom);
			addForm st id_form
		      end
		    else
		      Caret_option.debug ~dkey:dkey_accept
			"State %s refused ! %b -- %b"
			(simple_state st)
			(not(formInAtom form checked_atom))
			(formInAtom f2 checked_atom);
		  | _ -> assert false
	      )
	      rsm.until_set
	)
	r_mod.states
    )
    rsm.rsm_mod

let rec deleteUselessBranch state =
    (*if Caret_option.Simplify.get () = 2
      then*)
  if 
    (RState.Set.exists (fun s -> not (isDeleted s)) state.s_succs)
    && not(RState.Set.mem state state.s_succs)
  then () 
  else
    let () = Caret_option.debug ~dkey:dkey_simp "Deleting %s. Preds = %s" 
      (simple_state state) 
      (RState.Set.fold 
	 (fun s acc -> acc ^ "\n" ^ (simple_state s)) state.s_preds "" )
    in
    let preds = 
      state.s_preds
    in
    let () = deleteRState state
    in
    RState.Set.iter
      deleteUselessBranch
      preds

(* state -> exits *)
let entry_exit_tbl = RState.Hashtbl.create 106

let update_entry_exit_tbl visited_states exts = 
  RState.Set.iter
    (fun st -> 
      let old_bind = 
	try 
	  RState.Hashtbl.find entry_exit_tbl st
	with
	  Not_found -> RState.Set.empty
      in
      RState.Hashtbl.replace 
	entry_exit_tbl 
	st
	(RState.Set.union old_bind exts);
    )
    visited_states
    
let simplifyAutomaton rsm = 
  
  let () = Caret_option.feedback "Simplification" in
  let treated_modules = ref Rsm_module.Set.empty in
  let untreated_states = 
    ref 
      (Rsm_module.Set.fold
	 (fun rmod acc -> RState.Set.union acc rmod.states)
	 rsm.rsm_mod
	 RState.Set.empty
      ) in
  let rec simplifyModule r_mod = 
    
    let () = 
      treated_modules := Rsm_module.Set.add r_mod !treated_modules
	
    in
    
    let rec dfsInMod visited_states state = 
      
      if isDeleted state then raise Deleted
      else
	let () = 
	  untreated_states := RState.Set.remove state !untreated_states in
	if RState.Hashtbl.mem entry_exit_tbl state
	then 
	  update_entry_exit_tbl 
	      visited_states
	    (RState.Hashtbl.find entry_exit_tbl state)
	else
          if RState.Set.mem state visited_states
	  then 
	    Caret_option.debug ~dkey:dkey_simp
	      "State %s already visited"
	      (Caret_print.simple_state state)
	  else
	    if isExit state
	    then 
	      update_entry_exit_tbl 
		visited_states
		(RState.Set.singleton state)
	    else (* Not an exit *)

	      let at_least_one_path_ok = ref false 

		(* We set this to true if one execution of the following 
		   dfs without delete *)
	      in
	      if isCall state
	      then
		let box,entries = (Extlib.the state.call) 
		in
		
		let called_module = box.r_mod_repres
		in
		
		let () = simplifyModule called_module
		in
	        let corresp_returns = 
		  RState.Set.fold
		    (fun entry acc -> 
		      try 
			let exits = (RState.Hashtbl.find entry_exit_tbl entry)
			in
			RState.Set.fold
			  (fun ext acc2 -> 
			    let not_deleted_rets = 
			      RState.Set.filter
				(fun st -> not(isDeleted st))
				(throughBox ext box)
			    in
			    let () = (* We can update here the exits of the 
					box *)
			    box.b_exits <- 
			      (RState.Map.add 
				 ext 
				 not_deleted_rets 
				 box.b_exits)
			    in
			    RState.Set.union not_deleted_rets acc2)
			  exits 
			  acc
			  
		      with Not_found -> acc
		    )
		    entries
		    RState.Set.empty
		in
		if RState.Set.cardinal corresp_returns = 0
		then 
		  let () = Caret_option.debug ~dkey 
		    "%s does not have any reachable return : delete"
		    state.s_name
		  in
		  let () = deleteUselessBranch state in raise Deleted
		else 
		  begin
		    let () = 
		      RState.Set.iter
			(fun return -> 
			  try 
			    let () = 
			      mkSummaryTrans state return 
			    in
			    let () = 
			      dfsInMod 
				(RState.Set.add state visited_states) 
				return
			    in
			    at_least_one_path_ok := true
			  with
			    Deleted -> ()
			)
			corresp_returns
		    in 
		    if not !at_least_one_path_ok
		    then let () = deleteUselessBranch state in raise Deleted 
		  end
	      else (* Not an exit nor a call. We continue the dfs if we can *)
		let () = 
		  RState.Set.iter
		    (fun next -> 
		      try 
			let () = 
			  dfsInMod (RState.Set.add state visited_states) next
			in
			at_least_one_path_ok := true
		      with
			Deleted -> ()
		    )
		    state.s_succs
		in 
		if not !at_least_one_path_ok
		then let () = deleteRState state in raise Deleted 	
    in
    
	RState.Set.iter
	  (fun entry -> 
	    try dfsInMod RState.Set.empty entry 
	    with Deleted -> () (* todo : delete entry ? *))
	  (if isMainMod r_mod then rsm.start else r_mod.entries)
  in
  simplifyModule (getMainMod rsm);
  RState.Set.iter
    deleteRState
    !untreated_states
  
let degeneralizeAuto rsm = 
  
  (* To call iff there is more than one acceptance condition. *)
  
  let degen_rsm = mkEmptyRsm ("degen_" ^ rsm.name)
  in
 
  let mod_hashtbl =
    Rsm_module.Hashtbl.create 
      (Rsm_module.Set.cardinal rsm.rsm_mod)
  in
  
  (* formula -> elt -> copy of "elt" for the automaton "formula" *)

  let state_hashtbl = 
    Id_Formula.Hashtbl.create 
      (Id_Formula.Set.cardinal rsm.until_set)
  in
  
  let box_hashtbl = 
    Id_Formula.Hashtbl.create
      (Id_Formula.Set.cardinal rsm.until_set)
  in
    
  let init_mod_hashtbl () = 
    Rsm_module.Set.iter
      (fun m -> 
	Rsm_module.Hashtbl.add
	  mod_hashtbl
	  m
	  (mkModule 
	     ("copy_of_" ^ m.mod_name)
	     m.is_func
	  )
      )
      rsm.rsm_mod
  in
  (*
  let init_state_box_hashtbls formula = 
    Id_Formula.Hashtbl.add 
      state_hashtbl
      formula
      (RState.Hashtbl.create 103);
    
    Id_Formula.Hashtbl.add 
      box_hashtbl
      formula
      (Box.Hashtbl.create 41);
  in
  *)
  let rec copy_state states boxs s = 
    
    if RState.Hashtbl.mem states s
    then RState.Hashtbl.find states s
    else
    let n = new_sid () 
    in
    let new_state = 
      {
	s_name = "copy_" ^  (string_of_int n) ^ s.s_name;
	s_accept = s.s_accept ;
	call = 
	  (match s.call with
	    None -> 
	      None
	  | Some (b,set) -> 
	    Some (copy_box states boxs b, 
		  copy_set_state states boxs set));
	return =  	
	  (match s.return with
	    None -> 
	      None
	  | Some (b,set) -> 
	    Some (copy_box states boxs b, 
		  copy_set_state states boxs set));
	
	s_stmt = s.s_stmt ;
	s_atom = s.s_atom ;
	s_info = s.s_info;
	s_id = n ;
	s_mod = Rsm_module.Hashtbl.find mod_hashtbl s.s_mod ;      
	s_succs = copy_set_state states boxs s.s_succs ;
	s_preds = copy_set_state states boxs s.s_preds;
	summary_succs = copy_set_state states boxs s.summary_succs;
	summary_preds = copy_set_state states boxs s.summary_preds;
      } 
    in
    let () = RState.Hashtbl.add states s new_state
    in new_state

  and copy_set_state states boxs set_state = 
    RState.Set.fold 
      (fun s acc -> 
	RState.Set.add 
	  (copy_state states boxs s)
	  acc
      )
      set_state
      RState.Set.empty

      (* We will actually not copy the mod,
	 but complete the degeneralized one. *)

	
  and copy_box states boxs b = 
    if Box.Hashtbl.mem boxs b 
    then Box.Hashtbl.find boxs b
    else
      let new_id = new_bid () in
      let new_box = 
	{
	  b_id = new_id;
	  b_name = "copy_" ^ (string_of_int new_id) ^ b.b_name;
	  r_mod_repres = Rsm_module.Hashtbl.find mod_hashtbl b.r_mod_repres;
	  r_mod_belong = Rsm_module.Hashtbl.find mod_hashtbl b.r_mod_belong;
	  
	  box_atom = b.box_atom;
	  box_tag = b.box_tag;
	  
	  b_entries = 
	    RState.Map.fold
	      (fun key bind acc -> 
		RState.Map.add 
		  (copy_state states boxs key)
		  (copy_set_state states boxs bind)
		  acc
	      )
	      b.b_entries
	      RState.Map.empty;
	  	   
	  b_exits = 
	    RState.Map.fold
	      (fun key bind acc -> 
		RState.Map.add 
		  (copy_state states boxs key)
		  (copy_set_state states boxs bind)
		  acc
	      )
	      b.b_exits
	      RState.Map.empty;
	}
      in
      
      let () = Box.Hashtbl.add boxs b new_box 
      in new_box
  in

  
  let complete_degen_mod states boxs degen_mod m = 
    
    degen_mod.states <- 
      (RState.Set.union 
	 degen_mod.states
	 (copy_set_state states boxs m.states)
      );
    
    degen_mod.entries <- 
      (RState.Set.union 
	 degen_mod.states
	 (copy_set_state states boxs m.states)
      );

    degen_mod.exits <- 
      (RState.Set.union 
	 degen_mod.states
	 (copy_set_state states boxs m.states)
      )
  in
  let fill_new_modules formula = 
    Rsm_module.Hashtbl.iter
      (fun old_mod degen_mod -> 
	let st_tbl = Id_Formula.Hashtbl.find state_hashtbl formula
	  
	in
	let box_tbl = Id_Formula.Hashtbl.find box_hashtbl formula
	  
	in
	complete_degen_mod st_tbl box_tbl degen_mod old_mod)
      mod_hashtbl
  in
  
  init_mod_hashtbl ();
      
  degen_rsm.rsm_mod <- 
    (Rsm_module.Hashtbl.fold 
       (fun _ b acc -> Rsm_module.Set.add b acc)
       mod_hashtbl
       Rsm_module.Set.empty
    );
  
  Id_Formula.Set.iter
    (fun formula -> fill_new_modules formula)
    rsm.until_set;

  degen_rsm.start <- rsm.start;
  
(* Todo : transitions between acceptance conditions *)
  
  degen_rsm

let magic_backward_dataflow states =
  [RState.Set.choose states]

let acceptance_when_ends rsm = 
  assert (Caret_option.Main_ends.get ());
  let accept_card = Id_Formula.Set.cardinal rsm.until_set 
  in
  
  let main_mod = getMainMod rsm 
  in
  
  let accepting_states = 
    RState.Set.filter 
      (fun st -> match st.s_stmt.Cil_types.skind with
	Cil_types.Return _ -> 
	  (Id_Formula.Set.cardinal st.s_accept) = accept_card
      | _ -> false
      )
      (main_mod.states)
  in
  (* All the states in accepting_states are error states. We need to check if
     there is a path from Init to this state. The idea is that the whole 
     automaton is a counter-example : we will do a backward dataflow to
     refine it. *)
  
  (* magic_backward_dataflow : state -> state_list
     magic_backward_dataflow = lazy abstraction*)
  let accepting_path = 
    magic_backward_dataflow 
      accepting_states
  in
  if accepting_path = [] 
  then false 
  else true

  
(*    
 (* state -> exit -> paths from state to exit *)
  
(* State in Loop -> Loop Head of Loop -> Paths from State to Loop Head *)
let loop_memoizer = RState.Hashtbl.create 42
  
  
(* State before Loop -> Loop Head of Loop -> Paths from State to Loop Head *)
let path_to_loop_memoizer = RState.Hashtbl.create 42
   
(* Entry -> Exit -> Paths from Entry to Exit *)
let entry_exit_hashtbl = RState.Hashtbl.create 42
   

let exitReachability rsm = 
  let () = Caret_option.feedback "Exit reachability" in
  let treated_mod = ref Rsm_module.Set.empty
  in

  let rec update_table form_acc tbl zip_path exit_state = 
    try 
     
      match Zipper.get_right zip_path with
	State current_state -> 
	  let form_acc = 
	    Id_Formula.Set.union form_acc current_state.s_accept in
	  
	  let () = 
	    if Id_Formula.Set.is_empty current_state.s_accept then () 
	    else
	      Caret_option.debug ~dkey:dkey_exit 
		"State %s has accepting conditions %s.\nNew form acc : %s"
		(simple_state current_state)
		(Caret_print.string_raw_atom current_state.s_accept)
		(Caret_print.string_raw_atom form_acc)
	  in	  
	  let () = (* State current_state *)
	    Caret_option.debug ~dkey:dkey_exit 
	      "Table %s :\nRegistering path from\n--%s to\n--%s :\n%s\nAccepts : %s"
	      (if tbl == loop_memoizer then "loop_mem" 
	       else if tbl == path_to_loop_memoizer then "path_to_loop_mem"
	       else "entry_exit_mem")
	      (simple_state current_state)
	      (simple_state exit_state)
	      (List.fold_left 
		 (fun acc st ->
		   match st with State s -> acc ^"\n" ^ (simple_state s)
		   | Summary _ -> acc)
		 ""
		 zip_path.Zipper.left
	      )
	      (Caret_print.string_raw_atom form_acc)
	    ;

		  
	    in
	    let exit_hashtbl = 
	      try 
		RState.Hashtbl.find 
		  tbl
		  current_state
	      with
		Not_found -> 
		  let new_tbl = RState.Hashtbl.create 3 
		  in
		  let () = 
		    RState.Hashtbl.add
		      tbl
		      current_state
		      new_tbl
		  in new_tbl
	    in
	    let old_paths = 
	      try 
		RState.Hashtbl.find 
 		  exit_hashtbl
		  exit_state
	      with
		Not_found -> []
	    in
	    RState.Hashtbl.replace
	      exit_hashtbl
	      exit_state
	      (((zip_path.Zipper.left),form_acc)::old_paths);
	  update_table form_acc tbl (Zipper.move_right zip_path) exit_state
	    
      | Summary sum_list -> 
	let summ_acpt =
	  List.fold_left
	    (fun acc (_,acpt) -> Id_Formula.Set.union acpt acc)
	    form_acc
	    sum_list
	in
	let () = Caret_option.debug ~dkey:dkey_exit
	  "Summary path seen. Possible accepting conditions : %s"
	  (Caret_print.string_raw_atom  summ_acpt)
	in
	
	update_table 
	  summ_acpt
	  tbl 
	  (Zipper.move_right zip_path) 
	  exit_state
	
    with
      Failure "get_right" -> ()
      
  in
  
  let createSummarySuccs call rets = 
    let new_map = 
      RState.Map.merge
	(fun _ l1 l2 -> 
	  match l1,l2 with
	    Some i1, Some i2 -> Some (i1 @ i2)
	  | Some i, _ | _, Some i -> Some i
	  | _, _ -> None
	)
	call.summary_succs
	rets
    in
    call.summary_succs <- new_map
    ;
    RState.Map.iter
      (fun ret _ -> 
	ret.summary_preds <- RState.Set.add call ret.summary_preds)
      rets
  in
  
  let rec deleteUselessBranch state =
    (*if Caret_option.Simplify.get () = 2
      then*)
    if 
      (RState.Set.filter (fun s -> not(isDeleted s)) state.s_succs)
      <> RState.Set.empty
      && not(RState.Set.mem state state.s_succs)
    then () 
    else
      let () = Caret_option.debug ~dkey:dkey_exit "Deleting %s. Preds = %s" 
	(simple_state state) 
	(RState.Set.fold 
	   (fun s acc -> acc ^ "\n" ^ (simple_state s)) state.s_preds "" )
      in
      let preds = 
	state.s_preds
      in
      let () = deleteRState state
      in
      RState.Set.iter
	deleteUselessBranch
	preds
  in
  
  (*let forbidden_states = ref RState.Set.empty
  in
  *) 
  
  let rec unzip_until_f f zip = 
    try 
      let cur = Zipper.get_right zip 
      in
      if f cur then Zipper.move_right zip
      else unzip_until_f f (Zipper.move_right zip)
    with
      Failure "get_right" -> failwith "unzip"
  (* | _ -> unzip_until_f f (Zipper.move_right zip)*)
  (* ^^^^^^^^This bug deserves to be remembered^^^^^ *)

  in

  let memoized_as_loop visited_states state = 
    assert (RState.Hashtbl.mem loop_memoizer state);
    let loop_root_tbl = RState.Hashtbl.find loop_memoizer state
    in
    let () = Caret_option.debug ~dkey:dkey_exit ~level:2
      "State = %s. Visited_states = %s"
      (simple_state state)
      (Caret_print.string_path (List.map to_state visited_states))
    in
    
    RState.Hashtbl.iter
      (fun loop_root paths_to_loop_root -> 
	try
	let zipper_visited = 
	  unzip_until_f 
	    (function
	    | Summary _ -> false
	    | State s -> RState.equal s loop_root)
	    (Zipper.of_list visited_states)
	in
	let () = Caret_option.debug ~dkey:dkey_exit ~level:3
	  "Zipper content :\nLeft :\n%s\nRight :\n%s"
	  (Caret_print.string_path 
	     (List.map to_state zipper_visited.Zipper.left))
	  (Caret_print.string_path 
	     (List.map to_state zipper_visited.Zipper.right)) in
	  
	(* Zipper left contains path to state in the right order, 
	we need to reverse it and delete state (List.tl) *)

	List.iter 
	  (fun (path_to_loop_root,acpt) -> 
	    let zipper_to_use = 
	      if RState.equal loop_root state
	      then (* We registered the whoel loop, we don't
		      want it in the zipper *)
		Zipper.of_list (List.tl (List.rev zipper_visited.Zipper.left))
	      else
		{Zipper.left = (State state) :: path_to_loop_root; 
		 Zipper.right = List.tl (List.rev zipper_visited.Zipper.left)}
	    in
	    update_table 
	      acpt 
	      loop_memoizer 
	      zipper_to_use
	      loop_root)
	  paths_to_loop_root
	with
	  Failure "unzip" -> 
	    Caret_option.debug ~dkey:dkey_exit
	      "%s has not been visited"
	      (simple_state loop_root)
      )
      loop_root_tbl
  in
  let memoized_as_path_to_loop visited_states state = 
    assert (RState.Hashtbl.mem path_to_loop_memoizer state);
    let loop_root_tbl = RState.Hashtbl.find path_to_loop_memoizer state
    in
    RState.Hashtbl.iter
      (fun loop_root paths_to_loop_root -> 
	List.iter 
	  (fun (path_to_loop_root,acpt) -> 
	    let path_zipper = 
	      {Zipper.left = path_to_loop_root ; 
	       Zipper.right = ((State state)::visited_states)}
	    in
	    update_table 
	      acpt 
	      path_to_loop_memoizer 
	      path_zipper 
	      loop_root
	  )
	  paths_to_loop_root
      )
      loop_root_tbl
  in

  let memoized_as_reachable_exit visited_states state = 
    assert(RState.Hashtbl.mem entry_exit_hashtbl state);
    
    let exit_hashtbl = 
      RState.Hashtbl.find 
	entry_exit_hashtbl state
    in
    RState.Hashtbl.iter
      (fun exit_state path_list -> 
	List.iter 
	  (fun (path,acpt) -> 
	    let zipper_path = 
	      {Zipper.left = ((State state)::path); 
	       Zipper.right = visited_states}
	    in
	    update_table 
	      acpt 
	      entry_exit_hashtbl 
	      zipper_path 
	      exit_state
	  )
	  path_list
      )
      exit_hashtbl
  in  
  let is_loop_memoized state = 
    RState.Hashtbl.mem path_to_loop_memoizer state || 
      RState.Hashtbl.mem loop_memoizer state
  in

  let rec dfs visited_states start = 
    Caret_option.debug ~dkey:dkey_exit "State : %s"
      (simple_state start);
    let extend_start = State start in 
    
    if isDeleted start 
    then Caret_option.debug ~dkey:dkey_exit "Deleted, stop"
    else
      if is_loop_memoized start
      then 
	let () = Caret_option.debug ~dkey:dkey_exit
	  "Already treated, update of the memoizers" in
	let () = 
	  let () = Caret_option.debug ~dkey:dkey_exit
	    "As loop" in
	  try memoized_as_loop visited_states start
	  with 
	    Assert_failure _ -> () in
	
	let () = 
	  let () = Caret_option.debug ~dkey:dkey_exit
	    "As path to loop" in

	  try memoized_as_path_to_loop visited_states start
	  with Assert_failure _ -> () in
	
	try 
	  let () = Caret_option.debug ~dkey:dkey_exit
	    "As path to exit" in 
	  memoized_as_reachable_exit visited_states start
	with Assert_failure _ -> ()
      else
	let () = Caret_option.debug ~dkey:dkey_exit
	  "Never treated. Loop test over %s" 
	  (Caret_print.string_path (List.map to_state visited_states))in
	let zip_visit = 
	  try
	  unzip_until_f 
	    (fun st -> match
		st with 
		  Summary _ -> false
		| State s -> 
		  let () = Caret_option.debug ~dkey:dkey_exit
		    "Is %i equal\nto %i ?" 
		    (s.s_id)
		    (start.s_id)
		  in 
		  RState.equal s start)
	    (Zipper.of_list visited_states)
	  with Failure "unzip" -> 
	    Zipper.empty
	in

	if 
	  not (zip_visit.Zipper.right = []) 
	then 
	  (* then we saw a loop, saved in the left field of zip_visit *)
	  let () = Caret_option.debug ~dkey:dkey_exit
	    "New loop spotted" in
	  if 
	    (match start.s_stmt.Cil_types.skind 
	    with Cil_types.Loop _ | Cil_types.Goto _ | Cil_types.Return _
		-> false | _ -> true)
	  then Caret_option.debug ~dkey:dkey_exit "False loop detected"
	  else
	      
	    let () = (* Updating memoizers *)
	      let loop_zipper = 
		{Zipper.left = [extend_start];
		 Zipper.right = (List.rev zip_visit.Zipper.left)}
	      in
	      update_table 
		(Id_Formula.Set.empty) 
		loop_memoizer 
		loop_zipper 
		start;
	      let path_to_loop = 
		{Zipper.left = [extend_start];
		 Zipper.right = zip_visit.Zipper.right}
	      in
	      update_table 
		(Id_Formula.Set.empty) 
		path_to_loop_memoizer 
		path_to_loop 
		start
	    in
	    Caret_option.debug ~dkey:dkey_exit 
	      "Loop detected and memoizers updated"
	else (* Not a loop *)
	  let () = Caret_option.debug ~dkey:dkey_exit 
	      "Not a loop" in
	  if RState.Hashtbl.mem entry_exit_hashtbl start
	  then
	    let () = Caret_option.debug ~dkey:dkey_exit 
	      "State already treated as exit-reachable" in 
	    (* We update the entry_exit memoizer *)
	    memoized_as_reachable_exit visited_states start
   (*         let exit_hashtbl = 
	      RState.Hashtbl.find 
		entry_exit_hashtbl start
	    in
	    RState.Hashtbl.iter
	      (fun exit_state path_list -> 
		List.iter 
		  (fun path -> 
		    let zipper_path = 
		      {Zipper.left = (extend_start::path); 
		       Zipper.right = visited_states}
		    in
		    update_table entry_exit_hashtbl zipper_path exit_state
		  )
		  path_list
	      )
	      exit_hashtbl*)
	  else (* Not a loop and not studied yet *)
	    let () = 
	      Caret_option.debug ~dkey:dkey_exit 
		"State never treated as exit-reachable and is not a loop. Is it a call ?" in
            if isCall start && (RState.Map.is_empty start.summary_succs)
	    then (* calls are particular *)
	      let succs = treatCall start
	      in
	      
	      if RState.Map.is_empty succs
	      then deleteUselessBranch start
	      else
		let () = createSummarySuccs start succs;
		Caret_option.debug ~dkey:dkey_exit 
		  "Number of different return : %i"
		  (RState.Map.fold
		     (fun _ _ acc -> acc+1)
		     succs
		     0
		  )
		in

	        RState.Map.iter 
		  (fun ret paths -> 
		    dfs 
		      ((Summary paths)::extend_start::visited_states) 
		      ret)
		  succs
	    else
	      if isExit start
	      then 
	    (* We add to the visited states the current state *)
		update_table
		  (Id_Formula.Set.empty) 
		  entry_exit_hashtbl
		  (Zipper.of_list (extend_start::visited_states)) 
		  start
	      else
		if 
		  RState.Set.is_empty start.s_succs
		  && 
	            RState.Map.is_empty start.summary_succs
		  && 
		    (not(isMainMod start.s_mod) 
		     || 
		       match start.s_stmt.Cil_types.skind with
			 Cil_types.Return _ -> false
		       | _ -> true)
		    
		then deleteUselessBranch start
		else
		  begin 
		    if start.call = None then
		    RState.Set.iter 
		      (fun s -> dfs (extend_start::visited_states) s)
		      start.s_succs
		    
		    else

	            RState.Map.iter 
		      (fun key_return path_list -> 
			    dfs 
			      ((Summary path_list)
			       ::extend_start
			       ::visited_states)
			      key_return
		      )
		      start.summary_succs
		  end
    ;
    Caret_option.debug ~dkey:dkey_exit 
      "Done with state %s"
      (simple_state start)
		
  and treatCall state = 
    match state.call with
      None -> assert false
    | Some (box, entries) -> 
      (* We will check in entry_exit_hashtbl the summary successor of  *)
      let () =  
	if 
	  not (Rsm_module.Set.mem box.r_mod_repres !treated_mod)
	then
	  begin (* Mod treatment *)
	    Caret_option.debug ~dkey:dkey_exit 
	      "Mod %s discovered"
	      ( box.r_mod_repres.mod_name );
	    
	    RState.Set.iter 
	      (dfs [])
	      (throughBox state box);
	    treated_mod := 
	      Rsm_module.Set.add box.r_mod_repres !treated_mod;
	    Caret_option.debug ~dkey:dkey_exit 
	      "Mod %s treated, return to %s"
	      (box.r_mod_repres.mod_name)
	      (state.s_mod.mod_name)
	  end
	else ()
      in
      
      RState.Set.fold
	(fun entry main_acc -> 
	  try 
	    let entry_hashtbl = 
	      (RState.Hashtbl.find entry_exit_hashtbl entry)
		
	    in
	    
	    RState.Hashtbl.fold 
	      (fun ext_state paths acc -> 
		let ret_set = (throughBox ext_state box)
		in
		RState.Set.fold
		  (fun ret acc2 -> 
		    let old_bind = 
		      try 
			RState.Map.find 
			  ret acc2
		      with Not_found -> [] in
		    RState.Map.add ret (paths @ old_bind) acc2
		  )
		  ret_set
		  acc
	      )
	      entry_hashtbl
	      main_acc
	  with
	    Not_found (* entry_hashtbl *) -> main_acc
	)
	entries
        RState.Map.empty
	
  in
  RState.Set.iter
    (dfs []) rsm.start
  *)  
let print_extended_path path = 
  let rec __print deepness acc = function
    | (State s) :: tl -> 
        let acc = acc  ^ "\n" ^ deepness  ^ (simple_state s) in
	(__print
	   deepness 
	   acc 
	   tl)
	  
    | Summary paths :: tl -> 
      let deep_str = 
	List.fold_left 
	  (fun acc2 (path,acpt) -> 
	    (
	      "\nSummary path accepting:" ^
		(Id_Formula.Set.fold
		   (fun form acc -> 
		     (Id_Formula.varname form ) 
		     ^ acc ) 
		   acpt 
		   "")
	      ^ 
		__print 
		("<>" ^ deepness) 
		("") 
		path) 
	      
	    ^ "\n____\n"
	    ^ acc2
	  )
          ""
	  paths
      in
      __print deepness (acc ^ deep_str) tl
    | [] -> acc
  in
  __print "" "Path :" path
	  
let print_memoizer tbl = 
  RState.Hashtbl.iter
    (fun start finish_tbl -> 
      Caret_option.feedback
	"Starting with %s"
	(simple_state start);
      RState.Hashtbl.iter
	(fun finish paths ->
	  Caret_option.feedback
	    "Ending with %s"
	    (simple_state finish);
	  List.iter
	    (fun (path,acpt) -> 
	      Caret_option.feedback
		"%s"
		(print_extended_path path);
	      Caret_option.feedback
		"Satisfying %s"
		(Id_Formula.Set.fold
		   (fun form acc -> 
		     (Id_Formula.varname form)
		       ^ "\n"  ^ acc)
		acpt
		"")
		
	    )
	    paths
	)
	finish_tbl
    )
    tbl
    (*
let print_memoizers () = 
  
  List.iter 
    print_memoizer 
    [loop_memoizer; path_to_loop_memoizer ; entry_exit_hashtbl]

(*let testSimpleAcceptance rsm = 

  let main_mod = getMainMod rsm in
  
  let cardinal_accepting = Id_Formula.Set.cardinal rsm.until_set in

  let accepting_returns = 
    RState.Set.filter
      (fun st -> match st.s_stmt.skind with 
	Return _ -> Id_Formula.Set.cardinal st.s_accept = cardinal_accepting 
      | _ -> )
*)
    *)
let testAcceptance _ = None (*
  if Caret_option.Main_ends.get () then
    acceptance_when_ends rsm
  else 
    Caret_option.fatal 
      "Error : program doesn't ends : we don't treat it yet."*)
    
  (*try 
    analyse_paths rsm path_to_loop_memoizer loop_memoizer;
    None
  with
    Path_found (p,q) -> Some (p,q)
			 
  *)
