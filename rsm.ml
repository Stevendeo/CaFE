open Caretast  
open Formula_datatype
open Atoms
open Atoms_utils
open Rsmast
open Cil_types 

open Type_RState
open Type_Box
open Type_Rsm_module

exception Inconsistent_atom of atom_kind
exception Found of r_module 

module Sid = State_builder.SharedCounter(struct let name = "sid_counter" end)
module Mid = State_builder.SharedCounter(struct let name = "mid_counter" end)
module Bid = State_builder.SharedCounter(struct let name = "bid_counter" end)
module Rid = State_builder.SharedCounter(struct let name = "rsm_cpt" end)

let new_sid = Sid.next
let new_mid = Mid.next
let new_bid = Bid.next
let new_rid = Rid.next

let dkey = Caret_option.register_category "rsm:utils" 
(*let dkey_loop = Caret_option.register_category "rsm:loop" *)
let dkey_accept = Caret_option.register_category "rsm:accept"
let dkey_delete = Caret_option.register_category "rsm:delete"

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
	deleted = false;
	call = None ;     (* To change those, you need to *)
	return = None ;   (* use the plug functions *)
	s_stmt = stmt;
	s_atom = atom;
	s_info = info;
	s_id = n ;
	s_mod = r_mod;      
	s_succs = RState.Set.empty;
	s_preds = RState.Set.empty;
	summary_succs = RState.Map.empty;
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

let isDeleted state = state.deleted

let isAccepting rsm state = 
  (Id_Formula.Set.cardinal rsm.until_set) = Id_Formula.Set.cardinal state.s_accept

let isFinal state = 
  RState.Set.mem state state.s_succs

let rec deleteRState state =
  let () = 
    Caret_option.debug ~dkey:dkey_delete ~level:3
      "Deleting state %a"
      RState.pretty state in
  if isDeleted state then () else 
    
    (*state.s_stmt <- Cil.dummyStmt;*)
    let () = 
      state.s_name <- "DELETED";
      state.deleted <- true in
      let rmod = state.s_mod
      in
      let () =
	if isEntry state
	then
	  begin (* isEntry state *)
	    rmod.entries <- RState.Set.remove state rmod.entries;
      	    Box.Set.iter
	      (fun box -> 
		RState.Map.iter 
		  (fun call entry -> 
		    let new_set = (RState.Set.remove state entry) in
		    			
		    if RState.Set.is_empty new_set 
		    then 
		      let () = 
			box.b_entries <- RState.Map.remove call box.b_entries
		      in deleteRState call
		    else 
		      box.b_entries <- RState.Map.add 
			call 
		        new_set
			box.b_entries
		  )
		  box.b_entries)
	      rmod.box_repres
	  end (* isEntry state *)
	else if isExit state
	then
	  rmod.exits <- RState.Set.remove state rmod.exits
	else if isCall state
	then
	  begin
	    let box = (fst(Extlib.the state.call))
	    in
	    
	    box.b_entries <- RState.Map.remove state box.b_entries;
	    
	  end
	else if isRet state
	then 
	  begin
	    let () = Caret_option.debug ~dkey:dkey_delete ~level:5
	      "This is a return" in
	    let box = (fst(Extlib.the state.return))
	    in
	    
	    RState.Map.iter 
	      (fun ext rets -> 
		let new_set = (RState.Set.remove state rets) in
		if RState.Set.is_empty new_set 
		then 
		  box.b_exits <- 
		  (RState.Map.remove 
		     ext
		     box.b_exits)

		else 
		box.b_exits <- 
		  (RState.Map.add 
		     ext
		     new_set 
		     box.b_exits)		
	      )
	    box.b_exits;
	    
	    
	    let () = 
	      Caret_option.debug ~dkey:dkey_delete ~level:5 "Remaining exits : %i" 
	        (RState.Map.cardinal box.b_exits)  in
	    if RState.Map.is_empty box.b_exits
	    then 
	      RState.Map.iter 
		(fun call _ -> 
		  deleteRState call 
		)
		box.b_entries
	  end
	    
      in
      
      state.call <- None;
      state.return <- None;
      
      rmod.states <- RState.Set.remove state rmod.states;
      
      let () = 
	RState.Set.iter
	  (fun pred -> 
	      if RState.Set.cardinal pred.s_succs <= 1
	      then deleteRState pred 
	      else
		pred.s_succs <- RState.Set.remove state pred.s_succs
	  )
	  state.s_preds
      in
      RState.Set.iter
	(fun succ -> succ.s_preds <- RState.Set.remove state succ.s_preds)
	state.s_succs;
      
      state.s_succs <- RState.Set.empty;
      state.s_preds <- RState.Set.empty 
    
      
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

exception Fail_through_box
let throughBox state box = 
  
  try 
    if isCall state
    then RState.Map.find state box.b_entries
    else 
      if isExit state
      then RState.Map.find state box.b_exits
      else (raise Fail_through_box)
  with 
    Not_found -> RState.Set.empty
  | Fail_through_box -> raise Not_found

let getSuccs (state:RState.t) box = 
  match state.call with
    Some (call_b,_) -> throughBox state call_b
  | None -> 
    match box with 
      None -> state.s_succs
    | Some b -> 
      if RState.Set.is_empty state.s_succs
      then try throughBox state b with Not_found -> RState.Set.empty
      else state.s_succs

(** Transitions management *)

let mkTrans sta sto = 
  
  sta.s_succs <- RState.Set.add sto sta.s_succs;
  sto.s_preds <- RState.Set.add sta sto.s_preds

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

(* Copy primitives *)

let copyRState s = 
  let n = new_sid () 
    in
      {
	s_name = (string_of_int n) ^ s.s_name  ;
	s_accept = s.s_accept ;
	call = s.call ;       
	return = s.return ;   
	s_stmt = s.s_stmt ;
	s_atom = s.s_atom ;
	s_info = s.s_info;
	s_id = n ;
	s_mod = s.s_mod ;      
	s_succs = s.s_succs ;
	s_preds = s.s_preds;
	summary_succs = s.summary_succs;
	summary_preds = s.summary_preds;
	deleted = s.deleted;
    } 

let addMod r_mod rsm = rsm.rsm_mod <- Rsm_module.Set.add r_mod rsm.rsm_mod

let setStart state rsm = 
  let () = 
    Caret_option.debug ~dkey ~level:3 
      "Adding %a as a start" RState.pretty state in
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


(*let real_nexts box state = 
  (* box is in option, only in case state is an exit *)
  if state.call <> None
  then
    begin
      Caret_option.debug ~dkey "This is a call : ";
      let b,next = Extlib.the state.call in 
      Caret_option.debug 
	~dkey 
	"Box called : %s "
	(string_box b);
      [next]
  else 
    if isExit state
    then
      begin
	Caret_option.debug ~dkey "This is an exit";
	try 
	  Caret_option.debug 
	    ~dkey 
	    "Box returned from : %s "
	    (string_box box);
	  [throughBox state box]
	with
	  Failure _ (* hd *) | Not_found (* throughBox *) -> 
	    Caret_option.debug ~dkey "This exit is unplugged"
      end
    else 
      begin
	Caret_option.debug ~dkey "This is not an exit nor a call";
	state.s_succs
      end
      *)
(** Makes a dfs over the automaton. If an exception is raised in pre or post, 
    when pedantic is set to [true], Dfs_stopped will be raised. *)

let dfs ?(pre = fun _ _ -> ()) ?(post = fun _ _ -> ()) start = 
  Caret_option.debug ~dkey "Dfs for %s" (simple_state start);
  let visited_config = ref Config.Set.empty in
  (* Todo : in case of multiple starts, doesn't work *)
  let rec dfsRun  box_list state = 
    let () = 
      Caret_option.debug ~dkey "%s"
	(simple_state state)
    in
    let config =  
      state, box_list
    in
    let current_box = try Some (List.hd box_list) with _ -> None in
    
    if Config.Set.mem config !visited_config
    then 
      Caret_option.debug
	~dkey
	"Config %s already visited"
	(Config.varname config) 
    else
      let () = 
	Caret_option.debug
	~dkey
	"Config %s never visited"
	(Config.varname config)
      in
      let () = pre state current_box
      in
      let () =
	visited_config := Config.Set.add config !visited_config in 
      if isCall state
      then
	begin
	  Caret_option.debug ~dkey "This is a call : ";
	  let box,_ = Extlib.the state.call in 
	  
	  Caret_option.debug 
	    ~dkey 
	    "Box called : %s "
	    (string_box box);
	  
	  let nexts = throughBox state box in
     	  RState.Set.iter (dfsRun (box::box_list)) nexts
	end
      else 
	if isExit state
	then
	  begin
	    Caret_option.debug ~dkey "This is an exit";
	    try 
	      let box = List.hd box_list in
	      Caret_option.debug 
		~dkey 
		"Box returned : %s "
		(string_box box);
	      let nexts = throughBox state box in
	     
	      RState.Set.iter (dfsRun (List.tl box_list)) nexts
	    with
	      Failure _ (* hd *) -> assert false 
	    | Not_found (* throughBox *) -> 
		Caret_option.debug ~dkey "This exit is unplugged"
	  end
	else 
	  begin
	    Caret_option.debug ~dkey "This is not an exit";
	    RState.Set.iter (
	      fun st -> 
		(*try*)
		  dfsRun box_list st 
		(*with
		| _ -> if pedantic then raise Dfs_stopped else ()*)
	    ) state.s_succs
	  end;
      
      
      post state current_box
  in
  dfsRun [] start

let simplifyAutomaton rsm = 
  
  Caret_option.debug ~dkey "Starting the simplification";
  (* A state is not accessible if no transitions goes to it and is not callable
     (ie is not the beginning of a module). *)
  
  let state_accessible = ref RState.Set.empty in

  let useless_states = ref RState.Set.empty in

  let useful_exits = ref RState.Set.empty in

  let pre state _ = 
    if not(RState.Set.mem state !state_accessible)
    then
      begin
        
	Caret_option.debug ~dkey 
	  "RState %a accessible : computation. Succs = "
	  RState.pretty state;
	
	  (RState.Set.iter
	     (fun s -> 
	       Caret_option.debug ~dkey 
		 "%a" RState.pretty s) state.s_succs);
	
	state_accessible := RState.Set.add state !state_accessible
	  
      end	    
    else
      Caret_option.debug ~dkey "RState %a already treated" RState.pretty state;
    
  in
  
  let post state box =
    let succs = getSuccs state box
    in
    let is_exit = isExit state in
    let () = 
      if is_exit
      then 
	match box with
	  None -> assert false (* No exit for main *)
	| Some b -> 
	  if not (RState.Set.is_empty (throughBox state b))
	  then 
	    useful_exits := RState.Set.add state !useful_exits
    in
    let is_final_non_accept = (isFinal state) && (not (isAccepting rsm state)) and
	is_dead_end = 
      (RState.Set.for_all 
	 (fun succ -> RState.Set.mem succ !useless_states) 
	 succs)  && not(isCall state)
    in
    
    if (not is_exit) && (is_final_non_accept || is_dead_end) 
      (* If it is an exit, it might have a successor by another box *) 
    then 
      let () = 
	Caret_option.debug 
	  ~dkey 
	    "%a is useless because of 1 : %b 2 %b"
	    RState.pretty state 
	    is_final_non_accept 
	    is_dead_end;
	  
	  RState.Set.iter
	    (fun state ->  
	      Caret_option.debug ~dkey ~level:2 "Succ : %a\n" RState.pretty state) succs
	    
	in
	useless_states := RState.Set.add state !useless_states
	  
      else 
	let () = 
	  Caret_option.debug 
	    ~dkey 
	    "%a is not useless because of 1 : %b 2 %b"
	    RState.pretty state is_final_non_accept is_dead_end
	in
	RState.Set.iter
	  (fun state ->  
	    Caret_option.debug ~dkey ~level:2 "Succ : %a\n" RState.pretty state) succs
	  
	  
  in
  let () =
    Caret_option.debug ~dkey ~level:4 
      "Start of simplifiers : ";
    RState.Set.iter
      (fun s -> 
	Caret_option.debug ~dkey ~level:4 
	  "%a" RState.pretty s) rsm.start ;
    RState.Set.iter (dfs ~pre ~post) rsm.start ;  
    Caret_option.debug ~dkey "Dfs done !"
  in

  Caret_option.debug ~dkey "Starting suppression";

  Rsm_module.Set.iter
    ( fun r_mod -> 
      
      RState.Set.iter
	( fun state -> 
	  if not(RState.Set.mem state !state_accessible)
	    ||(RState.Set.mem state !useless_states)
	    ||(isExit state && not (RState.Set.mem state !useful_exits))
	    then deleteRState state
	)
	r_mod.states
    )

    rsm.rsm_mod;

  (* Deleting useless modules *)

  Rsm_module.Set.iter
    (fun rmod -> 
      let is_useless = 
	Box.Set.for_all 
	  (fun b -> 
	    RState.Map.is_empty b.b_entries || RState.Map.is_empty b.b_exits
	  )
	  rmod.box_repres
      in
      if is_useless
      then RState.Set.iter deleteRState rmod.exits
    )
    rsm.rsm_mod
    
