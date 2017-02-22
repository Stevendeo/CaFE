open Cil
open Cil_types
open Cil_datatype
open Rsmast
open Rsm
open Formula_datatype
open Formula_utils
open Caretast
open Atoms
open Atoms_utils

open Type_RState
open Type_Box
open Type_Rsm_module

exception Func_not_found
exception Not_Treated_Prev of (r_module * kernel_function * stmt)

type call = Mod of r_module | Fun of kernel_function

let dkey = Caret_option.register_category "caret_vis:module" 
let dkey_vis = dkey
let dkey_trans = Caret_option.register_category "caret_vis:trans"

let ignored_functions = ref []

let compute_ignored_functions () = 
  let fun_str = Caret_option.Ignore_fun.get () in
  let str_list = Str.split (Str.regexp ";") fun_str in
  ignored_functions := 
    List.map (fun func -> Globals.Functions.find_by_name func) str_list

 (* varinfo -> mod *)
let func_mod_hashtbl = 
  Varinfo.Hashtbl.create 9 

(* Module -> (Stmt -> RState set) *)

let mod_stmt_states_hashtbl:
    (((RState.Set.t) Stmt.Hashtbl.t) Rsm_module.Hashtbl.t) = 
  Rsm_module.Hashtbl.create 9

(* Call stmt -> Call state list,Return state list *)
let stmt_call_ret_hashtbl = Stmt.Hashtbl.create 14

(* A set containing the unreachable stmts  *)
let unreachable_stmts = ref Stmt.Set.empty

(* A list containing the states not treated until the end. It happens sometimes,
   frequently when there is if inside if. We need to treat them later. *)

let todo_states = ref []

let todoAdd info = 			      

  todo_states :=  info :: !todo_states

(** Create a list a states from a single statement. For each statement, we
    create the new state (stmt, atom, info) for each atom *)

let mkRStateSetFromStmt name stmt kf r_mod atoms = 

  let test atom = 
    (*(getAtomKind atom) = at_kind &&*) (isConsistent stmt kf atom)
  in
  if isMainMod r_mod
  then
    Atom.Set.fold
      (fun atom acc -> 
	if test atom
	then
	  let () = 
	  Caret_option.debug ~dkey ~level:1
	    "Atom %s accepted in stmt %s"
	    (Caret_print.string_atom atom)
	    (Caret_print.string_stmt stmt)

	  in
	  RState.Set.add
	    (mkRState 
	       ( name ^ (string_of_int stmt.sid)^"_inf" )
	       stmt
	       atom
	       (Tag Inf)
	       r_mod
	    ) 
	    acc
	else
	  let () = 
	  Caret_option.debug ~dkey ~level:1
	    "Atom %s not accepted in stmt %s"
	    (Caret_print.string_atom atom)
	    (Caret_print.string_stmt stmt)

	  in
	  acc )
      
      atoms
      RState.Set.empty

  else
    if Caret_option.Only_main.get () 
    then
      Atom.Set.fold
      (fun atom acc -> 
	if test atom
	then
	  RState.Set.add
	    (mkRState 
	       ( name ^ (string_of_int stmt.sid)^"_fin" )
	       stmt
	       atom
	       (Tag Fin)
	       r_mod
	    ) 
	    acc
	else acc )
	
	atoms
	RState.Set.empty

    else    Atom.Set.fold
	(fun atom acc -> 
	  if test atom
	  then
	    let inf_state = 
	      (mkRState 
		 ( name ^ (string_of_int stmt.sid)^"_inf" )
		 stmt
		 atom
		 (Tag Inf)
		 r_mod
	      )
	    in
	    RState.Set.add 
	      (mkRState 
	       ( name ^ (string_of_int stmt.sid)^"_fin" )
	       stmt
	       atom
	       (Tag Fin)
	       r_mod
	      )
	      (RState.Set.add inf_state acc)
	  else acc
	)
	
	atoms
	RState.Set.empty
        
let updateModStmtHashtbl r_mod stmt s_set = 
  
    try 
      let () = 
	Caret_option.debug ~dkey:dkey_vis ~level:2
	  "Registering %s in mod %s" 
	  (Caret_print.string_stmt stmt)
	  (Rsm_module.varname r_mod)
      in
	Stmt.Hashtbl.add 
	(Rsm_module.Hashtbl.find mod_stmt_states_hashtbl r_mod)
	stmt
	s_set;

	Caret_option.debug ~dkey:dkey_vis ~level:2
	  "Registered"

    with
      Not_found -> 
	let () =
	  Caret_option.debug ~dkey:dkey_vis ~level:2
	  "Registration failed" 
	in 	
	let mod_list = 
	  Rsm_module.Hashtbl.fold
	    (fun key_mod _ acc -> acc ^ "--" ^ (key_mod.mod_name))
	    mod_stmt_states_hashtbl
	    ""
	in
	Caret_option.debug 
	  ~level:3
	  ("Module seeked : %s \nList of modules registered : %s\n")
	  r_mod.mod_name  
	  mod_list;
	Caret_option.fatal
	  ~dkey
          ("Module not registered.")


	  
let rsm_create_modules rsm formula atoms = 

  (* We will check which atom can be a return atom, ie if it satisfies 
     absNextReq for another atom. 
     If not, we won't have to create the corresponding return state.
  *)

object(self)
  inherit Visitor.frama_c_inplace

  method! vglob_aux g = 
    match g with
    |GFun (fundec,_) ->
            
      let () = Caret_option.debug ~dkey 
	(*"Treatment of %a@"
	Cil_datatype.Varinfo.pretty fundec.svar*)
	"Treatment of %s" fundec.svar.vorig_name
      in
      let kf = Extlib.the self#current_kf in

      let vi = Kernel_function.get_vi kf in

      if (not (!Db.Value.is_called kf)) || (List.mem kf !ignored_functions)
      then 
	let () = Caret_option.debug ~dkey "%s is ignored"
	  vi.vorig_name
	in
	DoChildren

      else
      
	let new_mod = mkModule (vi.vname ^ "_rmod") vi in 
	let () = addMod new_mod rsm in
	let () = Varinfo.Hashtbl.add func_mod_hashtbl vi new_mod in
	let entry_stmt = Cil.mkEmptyStmt ~valid_sid:true () in
	let exit_stmt = Cil.mkEmptyStmt ~valid_sid:true () in

	let entry_states = 
	  Atom.Set.fold
	    (fun atom acc -> 
	      if 
		(isConsistent (List.hd fundec.sbody.bstmts) kf atom)
	      then
		begin
		  let new_state_fin = 
		    
		    (mkRState 
		       ( "entry" ^new_mod.mod_name^ "_fin" )
		       entry_stmt
		       atom
		       (Tag Fin)
		       new_mod
		    )
		      
		  in
		  
		  let new_state_inf = 
		    
		    (mkRState 
		       ( "entry" ^ new_mod.mod_name ^ "_inf" )
		       entry_stmt
		       atom
		       (Tag Inf)
		       new_mod
		    )
		  in	
		  (*let () = Rsm.addInfRState new_state_inf rsm in*)

		    if 
		      vi.vorig_name = "main"
		    then   
		      let () =
			if
			  formInAtom formula atom 
			  && (Id_Formula.Set.is_empty (callerFormulas atom))
			    
			then 
			  let () = 
			    Caret_option.debug
			      ~dkey
			      ~level:2
			      "%s is a start"
			      (Caret_print.simple_state new_state_inf)
			  in setStart new_state_inf rsm
			  
			else
			  Caret_option.debug
			    ~dkey
			    ~level:2
			    "%s is not a start : %b"
			    (Caret_print.simple_state new_state_inf)
			    (formInAtom formula atom)
		      in
		      new_state_inf::acc
		    else 
		      new_state_fin::new_state_inf::acc
		end
	      else acc
	    )
	    
	    (Hashtbl.find atoms IInt)
	    []
	    
	in 

	let exit_states = 

	  Atom.Set.fold
	    (fun atom acc -> 
	      	      
		(mkRState 
		   ("exit" 
		    ^ new_mod.mod_name ^ "_" 
		    ^ vi.vname ^ "_rmod")
		   exit_stmt
		   atom
		   TagR
		   new_mod 
		)::acc
	    )
	    (Hashtbl.find atoms IInt)
	    []
	  (*
	  List.fold_left
	    (fun acc atom -> 
	      
	      if 
		(getAtomKind atom) = IInt	        
	      then
		(List.fold_left
		   (fun acc2 atom2 -> 
		     if 
		       (getAtomKind atom2) = IRet 
		       && glNextReq closure atom atom2 
		     (* One of the requirements
			for an exit to have a 
			chance to be accessible.
			Check for LBLEXIT. *)
		     then
		       (mkRState 
			  ("exit" 
			   ^ (string_of_int new_mod.mid) ^ "_" 
			   ^ vi.vname ^ "_rmod")
			  exit_stmt
			  atom
			  (IProp atom2)
		       new_mod 
		       )::acc2
		     else
		       acc2
		   )
		   acc
		   possible_return_atom
		)
	      else acc
	    )
	    []
	    atoms*)
	in

	addEntries entry_states new_mod;
	addExits exit_states new_mod;
	
	(* We need to update our tables *)
	Rsm_module.Hashtbl.add 
	  mod_stmt_states_hashtbl 
	  new_mod
	  (Stmt.Hashtbl.create 19);

	DoChildren
	  
    | _ -> SkipChildren
    
end  
(* 
let (state_to_call_hashtbl: Atom.Set.t Atom.Hashtbl.t) = 
  Atom.Hashtbl.create (Atom.Set.cardinal atoms)

let (state_to_exit_hashtbl: Atom.Set.t Atom.Hashtbl.t) = 
  Atom.Hashtbl.create (Atom.Set.cardinal atoms)

let (ret_to_state_hashtbl: Atom.Set.t Atom.Hashtbl.t) =
  Atom.Hashtbl.create (Atom.Set.cardinal atoms)

(* A -> A' -> (t * t' * bool) list *)

let (state_to_state_hashtbl: 
       ((Rsmast.info * Rsmast.info) Atom.Hashtbl.t) Atom.Hashtbl.t) = 
  Atom.Hashtbl.create (Atom.Set.cardinal atoms)
*)
let createTransTo closure r_mod kf actual_stmt = 
  (* We have to create 4 kind of transitions :   
     - From states to calls
     - From states to exits 
     - From returns to states
     - What is left, state to state.
 
     Some of these tests have to be done many times, that's why we will save 
     our results in the previous hashtbl.*)

    let () = 
      Caret_option.debug 
	~dkey:dkey_trans 
	"Computation of transitions for states with statement %s" 
	(Caret_print.string_stmt actual_stmt) in
    let stmt_hshtbl = 
      try
	Rsm_module.Hashtbl.find mod_stmt_states_hashtbl r_mod
      with
	Not_found -> 
	  Caret_option.fatal 
	    "Module %s not registered properly. Modules registered : %s" 
	    (Rsm_module.varname r_mod)
	    (Rsm_module.Hashtbl.fold 
	       (fun key _ acc -> acc ^ "\n" ^ key.mod_name)
	       mod_stmt_states_hashtbl
	       "\n")
    in
    let state_set = 
      
      try 
	Stmt.Hashtbl.find stmt_hshtbl actual_stmt
      with
	
	Not_found -> 
	(* The actual statement is not registered in the statement hashtable,
	   we check the one containing only call statements. *)
	  
	try
	  fst (Stmt.Hashtbl.find stmt_call_ret_hashtbl actual_stmt)
	with
	  Not_found -> 
	    
	    let str_stmt_list = 
	      Stmt.Hashtbl.fold
		(fun stmt _ acc -> 
		  "-->\n" ^(Caret_print.string_stmt stmt)^ "\n" ^ acc)
		stmt_call_ret_hashtbl
		""
	    in
	    let str_stmt_list = 
	      Stmt.Hashtbl.fold
		(fun stmt _ acc -> 
		  "->\n" ^(Caret_print.string_stmt stmt)^ "\n\n" ^ acc )
		stmt_hshtbl
		str_stmt_list
	    in
	    Caret_option.debug ~dkey
	      "Statement seeked : %s\n Statements registered : %s"
	      (Caret_print.string_stmt actual_stmt)
	      str_stmt_list;
	    
	    Caret_option.fatal ~dkey
	      "Call/Ret Statement not registered. Don't forget to add the actual statement to the hashtable before creating the transitions"
    in

    let isFirstStmt stmt = 
      Stmt.equal 
	(Kernel_function.find_first_stmt kf)
        stmt
    in
    let prev_lists = 
      
      if isFirstStmt actual_stmt
      then 
	(* This is the first statement of the function *)
	let () = Caret_option.debug
	  ~dkey:dkey_trans
	  "This is the first statement of the function %s"
	  (Kernel_function.get_name kf)
	in	
	[r_mod.entries]
      else []
    in
    let prev_lists = 
	List.fold_left 
	  (fun acc prev_stmt -> 
	    let () = 
	      Caret_option.debug
		~dkey:dkey_trans
		"Previous statement : %s "
		(Caret_print.string_stmt prev_stmt) in
	    (* We need to test if a statement is accessible from a If stmt. For 
	       example, x=0; if (!x){f();} g(); -> g is not accessible directly
	       from the If stmt. *)
	    let is_direct_succ = (*	      
	      match prev_stmt.skind with
		If (exp,_,_,_) -> 
		  
		  let is_possible = 
		    !Db.Value.eval_expr 
		      ~with_alarms:CilE.warn_none_mode 
		      (Db.Value.get_stmt_state prev_stmt)
		      exp
		  in
		    (* If exp is possibly true & the statement is the first 
		       succ, or exp is never possible & the statement is not 
		       the first succ, then the transition is possible.*)
		  begin
		    ((Cvalue.V.contains_non_zero is_possible) 
		    && 
		      (List.hd prev_stmt.succs).sid = actual_stmt.sid)
		    ||
		      (not(Cvalue.V.contains_non_zero is_possible)
		       &&
			 ((List.hd prev_stmt.succs).sid <> actual_stmt.sid))
		  end
		    
	      | _ ->*) true
	    in
	    if is_direct_succ
	    then 
	      let prev_list = 
		try
		  (Stmt.Hashtbl.find stmt_hshtbl prev_stmt)
		with
		  Not_found -> 
			(* stmt_hshtbl doesn't contain prev_stmt, which means 
			   it should be a Call. For each Call, two kind of 
			   states were generated : calls and returns. If the 
			   previous statement A of a statement B is a Call, 
			   then B states needs a transition from return to 
			   them. *)
		    let () = Caret_option.debug
		      ~dkey:dkey_trans
		      "stmt not registered in stmt_hashtbl" 
		    in
		    let call_prev = 
		      try
			let res = 
			  snd
			    (Stmt.Hashtbl.find
			       stmt_call_ret_hashtbl 
			       prev_stmt)
			in let () = 
			     Caret_option.debug
			       ~dkey:dkey_trans
			       "But it is in the call_ret hashtbl. Example : %s"
			       (Caret_print.simple_state 
				  (RState.Set.choose res)
			       )
			   in res
		      with
			Not_found -> 
			      (* Last hope... is the statement reachable ? *)
			  if (Stmt.Set.mem prev_stmt !unreachable_stmts)
			  then RState.Set.empty
			  else 
				begin
				  let str_stmt_list = 
				    Stmt.Hashtbl.fold
				      (fun stmt _ acc -> 
					"->\n" ^
					  (Caret_print.string_stmt stmt)^
					  (string_of_int stmt.sid)^"\n\n" ^ acc )
				      stmt_hshtbl
				      ""
				  in
				  let str_stmt_list = 
				    Stmt.Hashtbl.fold
				      (fun stmt _ acc -> 
				    "-->\n" ^ 
				      (Caret_print.string_stmt stmt)^
				      (string_of_int stmt.sid)^"\n\n" ^ acc)
				      stmt_call_ret_hashtbl
				      str_stmt_list
				  in
				  Caret_option.debug ~dkey:dkey_trans
				    "Statement seeked : %s with id %d \n Statements registered : %s"				
				    (Caret_print.string_stmt prev_stmt)
				    prev_stmt.sid
				    str_stmt_list;
				  raise (Not_Treated_Prev (r_mod, kf ,actual_stmt))
				    
				end
		    in
		    call_prev
			  
	      in
	      let () = 
		Caret_option.debug 
		  ~dkey:dkey_trans "%i states" (RState.Set.cardinal prev_list)
	      in
	      prev_list::acc
	    else
	      acc
	  )
	  prev_lists
	  actual_stmt.preds
	  
    in
    
    (* If we are looking at the 1st statement of a function, we add the entry
       states. *)
    (*let prev_lists = 
      match kf.fundec with 
	Definition (fundec,_) -> 
	  if (List.hd fundec.sallstmts).sid = actual_stmt.sid
	  then r_mod.entries :: prev_lists
	  else prev_lists
      | Declaration _ -> assert false
    in
    *)
         
  (* Fourth case : Node to node. *)
    
   let nodeToNodeTest prev_state state = 
      Caret_option.debug 
	~dkey:dkey_trans ~level:2
	"Test nodeToNode : \n %s \n to %s ?"
	(Caret_print.string_atom prev_state.s_atom)
	(Caret_print.string_atom state.s_atom);
     
      let atom_prev = prev_state.s_atom in (* A *)
      let info_prev = prev_state.s_info in (* t *)
      
      let atom_state =  state.s_atom in (* A' *)
      let info_state = state.s_info in (* t' *)

       Caret_option.debug 
	~dkey:dkey_trans ~level:3
	"%b -- %b -- %b -- %b"
	(info_prev = info_state)
	(glNextReq closure atom_prev atom_state)
	(absNextReq closure atom_prev atom_state)
	(Id_Formula.Set.equal 
	   (callerFormulas atom_prev) 
	   (callerFormulas atom_state))
      ;
      
      info_prev = info_state 
      && glNextReq closure atom_prev atom_state
      && absNextReq closure atom_prev atom_state
      && (Id_Formula.Set.equal 
	    (callerFormulas atom_prev) 
	    (callerFormulas atom_state))
	
	
   (* First case : state.s_stmt = Instr (Call _ ) *)
   in
   let transToCallTest prev_state call_state = 
     

      Caret_option.debug 
	~dkey:dkey_trans ~level:2
	"Test transToCall";

    (* call_state is supposed to be a call, so call_state.box is not 
       empty. However, if the function is not registered (builtin for example), 
       it is just a simple state. *)
      if call_state.call = None
      then
	begin
	  Caret_option.debug
	    ~dkey:dkey_trans ~level:2
	    "This call state is not the call of a registered function.";
      nodeToNodeTest prev_state call_state
      end
      else
	begin
	  let atom_prev =  prev_state.s_atom in (* A *)
	  let info_prev =  prev_state.s_info in (* t *)
	  
	  
	  let box,_ = Extlib.the call_state.call in
	  let atom_box =  box.box_atom in (* A' *)
	  let info_box = Tag (box.box_tag) in (* t' *) 
	  
	  (* let atom_entry = call_state.s_atom in (* A'' *) *)
	  (*let info_entry = entry_state.s_info in (* t'' *)*)
	  let () = 
	    Caret_option.debug ~dkey:dkey_trans ~level:3
	      "%b %b %b %b %b"
	      (info_prev = info_box) 
	    (isConsistent actual_stmt ~after:false kf atom_box) 
	    (glNextReq closure atom_prev atom_box) 
	    (absNextReq closure atom_prev atom_box) 
	    (Id_Formula.Set.equal 
	       (callerFormulas atom_prev) 
	       (callerFormulas atom_box)) 
	  in
	  (info_prev = info_box) &&
	    (isConsistent actual_stmt ~after:false kf atom_box) && 
	    (glNextReq closure atom_prev atom_box) &&
	    (absNextReq closure atom_prev atom_box) &&
	    (Id_Formula.Set.equal 
	       (callerFormulas atom_prev) 
	       (callerFormulas atom_box)) 
	    
	end
    (*
      && glNextReq closure atom_box atom_entry
      && (let temp_list = 
      List.filter
      (fun form -> match form with 
      CNext(Past,f) -> 
      List.mem f atom_box
      | _ -> false)
      closure 
      in equivList atom_entry temp_list) *)
	
    (* The previous tests are done during the call state creation, as their 
       validity don't depend on the next state. Check for LBLCALLTEST *)
	  
    and transToExitTest return_state exit_state =  
    
    (* Second case : state.s_stmt has no successors. 
       Those statements are not considered as exit statements, we need to 
       create two trans : from prevs to returns and from returns to exit. 
       If a return does not satisfies the needed properties, none of these 
       trans will be created. Also, we consider the transition 
       prev -> return stmt as a node to node transition (4th case) *)

      Caret_option.debug 
	~dkey:dkey_trans ~level:2
	"Test transToExit";
      let atom_ret = return_state.s_atom in (* A *)
      let info_ret = return_state.s_info in (* t *)
      
      let atom_exit = exit_state.s_atom in (* A' *)
      (*let info_exit = match exit_state.s_info with (* R *)
	  IProp a -> a 
	| Tag _ -> 
	  Caret_option.fatal 
	    ~dkey 
	    "This state is not associated to an exit." 
      in*)
      (info_ret = Tag Fin) &&
	(glNextReq closure atom_ret atom_exit) &&
	(absNextReq closure atom_ret atom_exit) &&
	(Id_Formula.Set.equal 
	  (callerFormulas atom_ret) 
	  (callerFormulas atom_exit)) &&
	(not(
	  Id_Formula.Set.exists 
	    (fun form -> 
	      match getFormula form with
		CNext (Abstract,_) -> true
	      | _ -> false
	    )
            (getPropsFromAtom  atom_exit)))
      
      (*&& let test? = (glNextReq closure atom_exit info_exit) *) 
      (* Can be tested at creation, check for LBLEXIT*)
      
  (* Third case : ret to states. Ret is here to describe the "after_call" 
     state, which is not represented by a statement in the source code. *)
    and retToNodeTest prev_state state = 
    
      Caret_option.debug 
	~dkey:dkey_trans ~level:2
	"Test retToNode";
      if prev_state.return = None
      then
	begin
	  Caret_option.debug
	    ~dkey:dkey_trans ~level:2
	    "This return state is not the return of a registered function.";
	  nodeToNodeTest prev_state state
      end
      else


      let prev_box,_ = Extlib.the prev_state.return in
      
    (* let box_atom = prev_box.box_atom in *) (* A *)
      let box_info = prev_box.box_tag in (* t *)
      
    (* let exit_atom = exit_state.s_atom in *) (* A' *)
      let exit_info = (* R *)
        prev_state.s_atom
      in
      
      let state_atom = state.s_atom in (* A'' *)
      let state_info = state.s_info in (* t'' *)
      (*Caret_option.debug
	~dkey:dkey_trans
	"%b -- %b -- %b -- %b "
	(state_info = Tag box_info)
	(glNextReq closure exit_info state_atom)
	(absNextReq closure exit_info state_atom)
	(Id_Formula.Set.equal
	   (callerFormulas exit_info) 
	   (callerFormulas state_atom));*)
      (state_info = Tag box_info)
       (* && absNextReq closure box_atom exit_atom 
       && (equivList 
       (callerFormulas box_atom) 
       (callerFormulas exit_atom)) 
       && (isConsistent actual_stmt ret_atom)*)
	
    (* The previous tests are done during the state creation, as their validity 
       don't depend on the next state. Check for LBLRETTEST. *) 
      && glNextReq closure exit_info state_atom
      && absNextReq closure exit_info state_atom
      && (Id_Formula.Set.equal
	   (callerFormulas exit_info) 
	   (callerFormulas state_atom)) 
	
   in
   
   let modificationTest pre_state post_state = 
     match post_state.s_stmt.skind with
     
       (*Instr (Set ((Var var,_),_,_)) -> 
	 noSideEffectNextReq 
	   ~var 
	   pre_state.s_atom
	   post_state.s_atom true*)
     | Instr (Set _) -> true
     | Instr (Call (Some _,_,_,_)) -> true 
     | Instr (Call (None,{enode = Lval (Var v, _)},_,_)) -> 
       let func = 
	 Globals.Functions.find_by_name v.vorig_name in 
       not(List.mem func !ignored_functions)

     (* todo : test if there is really a modification *)
     | Instr (Asm _) -> 
       Caret_option.debug 
	 ~dkey:dkey_trans 
	 ~level:2
	 "ASM not supported"; true
	 
     | Instr _        
     | Goto _ 
     | Break _ 
     | Continue _ 
     | If _ 
     | Switch _  
     | Loop _ 
     | Block _  
     | Return _ 
     | Throw _ | TryCatch _ | TryFinally _ | TryExcept _ -> 
       (* In this case, there is no modification 
		  of any variable : we check if the atomic 
		  properties are the same *)
       noSideEffectNextReq 
	 pre_state.s_atom
	 post_state.s_atom

     | UnspecifiedSequence _ -> true
   in

   let treatRStates goodTest start_set next_set = 
     let () = 
       Caret_option.debug 
	 ~dkey:dkey_trans
	 "link %i states\nto %s:%i states"
	 (RState.Set.cardinal start_set)
	 (Caret_print.string_stmt (RState.Set.choose next_set).s_stmt)
	 (RState.Set.cardinal next_set)
     in
     
     RState.Set.iter
       (fun start_state -> 
	 let () = 
	   Caret_option.debug 
	     ~dkey:dkey_trans
	     ~level:1
	     "%s : test with %i states"
	     (Caret_print.simple_state start_state)
	     (RState.Set.cardinal next_set)
	 in
	 RState.Set.iter
	   (fun next_state -> 
	     Caret_option.debug 
	       ~dkey:dkey_trans ~level:2
	       "Test of :\n%s\nWith atom :\n %s\n-> %s\n with atom n%s :"
	       (Caret_print.simple_state start_state)
	       (Caret_print.string_atom start_state.s_atom)
	       (Caret_print.simple_state next_state)
	       (Caret_print.string_atom next_state.s_atom)
	      ;
	     
	     if 
	       (not (modificationTest start_state next_state))
		 
	     then
	       Caret_option.debug 
		 ~dkey:dkey_trans ~level:2
		 "Fail as there is no modification but the %s"
		 "atomic properties are different"
	     else
	      if (goodTest start_state next_state) 
	      then begin
		Caret_option.debug 
		  ~dkey:dkey_trans ~level:2
		  "Success";

		  (Rsm.mkTrans start_state next_state) end
	      else
		Caret_option.debug 
		  ~dkey:dkey_trans ~level:2
		  "Fail"
		  
	    )
	    
	    next_set
	)
	
	start_set;
    in
    
    let treatCall prev_is_ret prev_states = 
      let goodTest = 
	if prev_is_ret 
	then (fun prev cur -> 
	  (*Caret_option.debug 
	    ~dkey:dkey_trans
	    "retToNodeTest & transToCall done";*)
	  (retToNodeTest prev cur) && (transToCallTest prev cur))
	else 	  
	  begin 
	    Caret_option.debug 
	      ~dkey:dkey_trans ~level:2
	      "transToCall done : prev_state size = %d, actual = %d"
	      (RState.Set.cardinal prev_states)
	      (RState.Set.cardinal state_set); 
	    transToCallTest 
	  end
      in
      treatRStates goodTest prev_states state_set
    in
    let treatNormal prev_is_ret prev_states = 
      
      let goodTest = 
	if prev_is_ret 
	then 
	  begin
	    Caret_option.debug 
	      ~dkey:dkey_trans ~level:2
	      "retToNode done";
	    retToNodeTest 
	  end
	else 
	  begin
	    Caret_option.debug 
	      ~dkey:dkey_trans ~level:2
	      "ToNode done";
	    nodeToNodeTest 
	  end
      in 
      treatRStates goodTest prev_states state_set

    in
    
    let treatRet prev_is_ret prev_states = 
      Caret_option.debug  ~level:2
	~dkey:dkey_trans
	"In treatToRet : ";
      let () = treatNormal prev_is_ret prev_states in
      let goodTest = transToExitTest 
      (*
	if prev_is_ret 
	then (fun cur ext -> 
	(retToNodeTest prev cur) && (transToExitTest cur ext))
	
	else (fun prev cur ext -> 
	(nodeToNodeTest prev cur) && (transToExitTest cur ext))*)
      in
      
      let exit_states = r_mod.exits in
      
      (treatRStates goodTest state_set exit_states)

    in
    
    Caret_option.debug 
      ~dkey:dkey_trans ~level:2
      "Computing transitions for statement %s" 
      (Caret_print.string_stmt actual_stmt);
    let () = 
      List.iter
	
	(fun prev_states -> 
	  
	(* Tests if the previous states are states returning from a call. 
	   If so, retToNodeTest must be done. *)
	  Caret_option.debug 
	    ~level:3 
	    ~dkey:dkey_trans
	    "Computing from the %i previous states" 
	    (RState.Set.cardinal prev_states);
	  let prev_is_ret = 
	    try
	      isRet (RState.Set.choose prev_states) 
	    with
	      Not_found -> false (* false because, well, there's nothing *)
	  in
	  
	  if actual_stmt.succs = []
	    (* The end of a function is always a return in Cil*)
	  then
	    begin
	    Caret_option.debug 
	      ~dkey:dkey_trans
	      "Statement %s is the end of a function" 
	      (Caret_print.string_stmt actual_stmt);
	      treatRet prev_is_ret prev_states
	    end
	  else
	    begin
	      Caret_option.debug 
	      ~dkey:dkey_trans
	      "Statement %s is not the end of a function"
	      (Caret_print.string_stmt actual_stmt);

	      Caret_option.debug 
	      ~dkey:dkey_trans
	      "Succs :\n%s"
	      (List.fold_left
		(fun acc stmt-> acc ^ "\n" ^ (Caret_print.string_stmt stmt))
		  ""
		  actual_stmt.succs
	      ); 
	      
	    match actual_stmt.skind with
	    
	    Instr ( Cil_types.Call _ ) -> 
	      Caret_option.debug 
		~dkey:dkey_trans
		"Statement %s is a Call" 
		(Caret_print.string_stmt actual_stmt);
	      treatCall prev_is_ret prev_states	    
		
	  | Return _ -> 
	      Caret_option.debug 
		~dkey:dkey_trans 
		"Statement %s is a Return" 
		(Caret_print.string_stmt actual_stmt);
	    treatRet prev_is_ret prev_states
	      
	  | _ -> 
	    Caret_option.debug 
	      ~dkey:dkey_trans
	      "Statement %s is not a Call nor a Return" 
	      (Caret_print.string_stmt actual_stmt);
	    treatNormal prev_is_ret prev_states
	      
	    end
	)
	prev_lists
    in ()  

let rsm_create_states closure atoms = 

object(self)
  inherit Visitor.frama_c_inplace

  method! vstmt_aux stmt = 
    
    let () =  
      Caret_option.debug ~dkey:dkey_vis
	"Statement treated : %s with id %d"
	(Caret_print.string_stmt stmt)
	stmt.sid
    in
  
    let kf = Extlib.the self#current_kf in
    
    if List.mem kf !ignored_functions
    then SkipChildren
    else
    
    let vi = Kernel_function.get_vi kf in
    
   (* 
    if (Cil.is_builtin vi) (* || not(Db.Value.is_reachable state)*)
    then 
      let () =  
	Caret_option.debug ~dkey:dkey_vis ~level:2
	  "The studied function is a builtin, we don't treat it yet."
      in
      SkipChildren
	
    else
   *)
    let state = Db.Value.get_stmt_state stmt in
    if not(Db.Value.is_reachable state)
    then 
      let isret = function | Return _ -> true | _ -> false in 
      let () = 
	if
	  (Caret_option.Main_ends.get ()) 
	  && not(Db.Value.is_reachable_stmt stmt)
	  && (*isMainMod ref_current_mod*) vi.vorig_name = "main"
	  && (isret stmt.skind)
	then
	  Caret_option.fatal "According to value, the program doesn't end"
	    
      in
      let () =  
	Caret_option.debug ~dkey:dkey_vis ~level:2
	  "Value says this state is unreachable, we won't treat it."
      in
      unreachable_stmts := Stmt.Set.add stmt !unreachable_stmts;
      DoChildren
    else
      let () = Caret_option.debug ~dkey:dkey_vis ~level:2
	"Value says this state reachable."
      in
      let ref_current_mod = 
	try
	Varinfo.Hashtbl.find 
	  func_mod_hashtbl 
	  vi
      with
	Not_found -> 
	  Caret_option.fatal 
	    "Error : %s has not been registered properly"
	  vi.vorig_name
      in
      
      
      
      let doChildrenPostWithTrans () = 
	  DoChildrenPost
	    (fun stmt ->
	      begin
		try
		  (createTransTo closure ref_current_mod kf stmt);
		  stmt
		with 
		  Not_Treated_Prev info -> 
		    todoAdd info;
		    stmt
	      end
	    )
      in
      let string_of_stmt = string_of_int stmt.sid 
      in
      
      let treatInstr stmt i = 
	match i with 
	  Set _ -> 
	    let () =  
	      Caret_option.debug ~dkey:dkey_vis ~level:2
		"Statement is a set."
	    in
	    let set_states = 
	      mkRStateSetFromStmt 
		("set_" ^ string_of_stmt) 
		stmt
		kf
		ref_current_mod
		(Hashtbl.find atoms IInt)
		
	    in
	    
	    addRStates 
	      set_states	    
	      ref_current_mod;
	    
	    updateModStmtHashtbl ref_current_mod stmt set_states;
	    
	    doChildrenPostWithTrans ()
	| Call (_, expr, _, _) -> 
	  let () =  
	    Caret_option.debug ~dkey:dkey_vis ~level:2
	      "Statement is a call."
	  in
	  let rec rmv_info e = match e.enode with
	      Info (ex,_) -> rmv_info ex
	    | CastE (_,ex) -> rmv_info ex
	    | AlignOfE ex -> 
	      Caret_option.debug 
		~dkey:dkey_vis 
		"Careful, AlignOfE";
	      rmv_info ex
	    | Lval (Mem e,_) -> 
	      Caret_option.debug 
		~dkey:dkey_vis ~level:2
		"Careful, this is a function pointer.";
	      rmv_info e
	    | _ -> e
	  in
	  let expr = rmv_info expr in
	  begin
	    match expr.enode with 
	      Lval (Var v_info, _) 
	    | AddrOf (Var v_info, _) 
	    | StartOf (Var v_info, _) -> 
		(*  if Cil.is_builtin v_info
		  then
		    let () = 
		      Caret_option.debug ~dkey:dkey_vis
			"Built_in functions are ignored"
		    in
		    let cur_states = 
		      mkRStateSetFromStmt 
			("int_" ^ string_of_stmt) 
			stmt
			kf
			ref_current_mod
			(Hashtbl.find atoms IInt)
			
		    in 
		    
		    let () = addRStates cur_states ref_current_mod in
		    let () = updateModStmtHashtbl ref_current_mod stmt cur_states in
		    doChildrenPostWithTrans ()
		      
		  else *)
		    begin
		      let callable = 
			Db.Value.call_to_kernel_function stmt
		      in
		      
		      let mods_repres =
			
			Kernel_function.Hptset.fold
			  (fun k_f acc -> 
			    try
			      (Mod 
				((Varinfo.Hashtbl.find 
				 func_mod_hashtbl
				 (Kernel_function.get_vi k_f)))) :: acc
			    with 
			      
			      Not_found -> 
			  (* We found a new function, ignored during 
			     the first visit. We need to treat this call (and
			     the associated return).
			  *)
				(Fun k_f) :: acc
			  )
			  callable
			  []
		      in
		      if mods_repres = []
		      then 
			(*let fun_list =
			  Varinfo.Hashtbl.fold
			    (fun vi _ acc -> acc ^ " -- " ^ (vi.vname) )
			    func_mod_hashtbl
			    ""
			in
			let str_callable = 
			  Kernel_function.Hptset.fold
			    (fun k_f acc -> 
			      (((Kernel_function.get_vi k_f)).vname) ^  acc
			    )
			    callable
			    ""
			in
			Caret_option.debug ~dkey ~level:3
			  "Functions seeked : %s\n Functions registered : %s\n"
			  str_callable
			  fun_list;
			*)
			raise Func_not_found
		      else
			let call_set,return_set = 
			  List.fold_left 
			    (fun (acc_c,acc_r) -> function
			    | Fun called -> 
			      begin
			      (* We treat it as a pair of states call and return *)
			      let fun_name = Kernel_function.get_name called
			      in
			      
			      let call_atom_set = 
				try Hashtbl.find atoms (ICall (Some fun_name)) 
				with
				  Not_found -> Hashtbl.find atoms (ICall None)

			      in
			      
			      let ret_atom_set = 
				try Hashtbl.find atoms (IRet (Some fun_name)) with
				  Not_found -> Hashtbl.find atoms (IRet None)
			      in
			      let calls = 
				Atom.Set.fold
				  (fun call_atom acc -> 
				    if 
				      isConsistent 
					stmt 
					~after:false 
					kf 
					call_atom
				    then 
				      RState.Set.add
					(mkRState
					   ("call_" ^ fun_name) 
					   stmt
					   call_atom
					   (Tag Inf)
					   ref_current_mod )
					(RState.Set.add 
					   (mkRState
					      ("call_" ^ fun_name) 
					      stmt
					      call_atom
					      (Tag Fin)
					      ref_current_mod )
					   acc)
				    else acc
				  )
				  call_atom_set
				  RState.Set.empty
			      in
			      let rets = 
				Atom.Set.fold
				  (fun ret_atom acc -> 
				    if
				      isConsistent stmt ~after:true kf ret_atom

				    then 
				      RState.Set.add
					(mkRState
					    ("return_" ^ fun_name) 
					   stmt
					   ret_atom
					   (Tag Inf)
					   ref_current_mod)
				      (
				      RState.Set.add 
					(mkRState
					   ("return_" ^ fun_name) 
					   stmt
					   ret_atom
					   (Tag Fin)
					   ref_current_mod
					)
					acc)
				    else acc
				  )
				  ret_atom_set
				  RState.Set.empty
			      in
			      
			      let () = 
				RState.Set.iter
				  (fun call -> 
				    let call_atom = call.s_atom in
				    RState.Set.iter
				      (fun ret -> 
					let ret_atom = ret.s_atom in
					if
					  glNextReq closure call_atom ret_atom
					  &&
					    absNextReq closure call_atom ret_atom
					  && 
					    (Id_Formula.Set.equal 
					       (callerFormulas call_atom)
					       (callerFormulas ret_atom)
					    )
					  && call.s_info = ret.s_info
					then mkTrans call ret
				      )
				      rets				    
				  )
				  calls in
			      (* addRStates calls ref_current_mod;
			      addRStates rets ref_current_mod;

			      Stmt.Hashtbl.add 
				stmt_call_ret_hashtbl 
				stmt 
				(calls, rets) 
			      in
			      doChildrenPostWithTrans ()*)
				((RState.Set.union calls acc_c),(RState.Set.union rets acc_r))
			      end
			    | Mod mod_repres -> 
			      Atom.Set.fold 
				(fun box_atom (acc_call , acc_ret) -> 
				if not (isConsistent stmt ~after:false kf box_atom)
				then (acc_call , acc_ret)
				else
				(* A call is a state in which the "call" 
				   parameter 
				   is (box, entry). Each entry has already been 
				   created during the globals visit, so the atom of
				   each call state should correspond to the entry 
				   atom. *)
				(*if 
				  not(isACall box_atom) 
				  || not (isConsistent stmt kf box_atom)
				  
				  then
				  (acc_call , acc_ret)
				  else *)
				let entry_list = 
				  mod_repres.entries
				in
				
				let box_list = 
				  if Caret_option.Only_main.get ()
				  then 
				    if isMainMod ref_current_mod 
				    then
				      [(mkBox 
					  ("box_" ^ mod_repres.mod_name ^ "_inf")
					  mod_repres
					  ref_current_mod
					  box_atom
					  Inf)]
				    else 
				      [(mkBox 
					  ("box_" ^ mod_repres.mod_name ^ "_fin")
					  mod_repres
					  ref_current_mod
					  box_atom
					  Fin)]
				  else
				    [(mkBox 
					("box_" ^ mod_repres.mod_name ^ "_fin")
					mod_repres
					ref_current_mod
					box_atom
					Fin) ;
				     
				     (mkBox 
					("box_" ^ mod_repres.mod_name ^ "_inf")
					mod_repres
					ref_current_mod
					box_atom
					Inf)]
				      
				in
				let call_list =
				  List.fold_left
				    (fun acc box -> 
				      
				      let state = 
					mkRState
					  ("call_" ^ mod_repres.mod_name) 
					  stmt
					  box_atom
					  (Tag box.box_tag)
					  ref_current_mod
				      in
				      let () = 
					let temp_list = 
					  List.fold_left
					    (fun acc id_form -> 
					      let form = 
						getFormula id_form 
					      in
					      match form with 
						CNext(Past,f) -> 
						  if 
						    formInAtom 
						      f 
						      box_atom
						  then 
						    Id_Formula.Set.add 
						      (findFormula 
							 f 
							 closure)
						      acc 
						      
						  else acc
					      | _ -> acc)
					    Id_Formula.Set.empty
					    closure
					in 
					RState.Set.iter
					  (fun entry -> 
					    if
					    (* LBLCALLTEST *)
					      
					      (glNextReq 
						 closure box_atom entry.s_atom)
					      && (
						Id_Formula.Set.equal
						  (callerFormulas entry.s_atom) 
						  temp_list
					      )
					      &&
						begin
						  (not 
						     (entry.s_info = Tag Inf)) 
						  || 
						    ((entry.s_info = Tag Inf)  
						     && not(
						       Id_Formula.Set.exists 
							 (fun form ->  
							   match getFormula 
							     form 
							   with
							     CNext(Abstract,_) -> true
							   | _ -> false 
							 )
							 (getPropsFromAtom box_atom)
						     )
						    )
						    
						end
						
					    then
					      plugEntryBox box state entry
					  )
					  entry_list
				      in
				      
				      RState.Set.add state acc
					
				    )
				    RState.Set.empty
				    box_list
				in
				
				if RState.Set.cardinal call_list = 0
				then 
				  acc_call,acc_ret 
			      (* No state allows to call the box *)
				else 
				  
				  let call_list =
				    RState.Set.union acc_call call_list 
				  in
				  
				  let exit_list = mod_repres.exits 
				  in
				  
				  let ret_list =
				    
			            Atom.Set.fold
				      (fun ret_atom acc -> 
					
					if 
					  begin (* LBLRETTEST *)
					  (* (isARet ret_atom) 
					     && *)(absNextReq 
						     closure 
						     box_atom 
						     ret_atom
					   )
					    && (Id_Formula.Set.equal
						  (callerFormulas box_atom) 
						  (callerFormulas ret_atom)) 
					    && 
					    (isConsistent 
					       stmt
					       kf 
					       ret_atom)
					(* && (noSideEffectNextReq 
					   box_atom 
					   ret_atom) *)
					  end
					then
					  
					  
					  List.fold_left
					    (fun acc2 box -> 
					      let return = 
						(mkRState
						   ("return_" ^ mod_repres.mod_name) 
						   stmt
						   ret_atom
						   (Tag box.box_tag)
						   ref_current_mod)
					      in
					      let () =
						(RState.Set.iter
						   (fun ext -> 
						     if 
						       glNextReq 
							 closure 
							 ext.s_atom
							 ret_atom
						     then 
						       plugExitBox box ext return
							 
							 
						   )
						   
						   exit_list
						)
					      in
					      RState.Set.add return acc2
					    )
					    acc
					    box_list
					    
					else
					  acc
				      )
				      (try
					 (Hashtbl.find atoms (IRet (Some v_info.vname)))
				       with Not_found -> 
					 (Hashtbl.find atoms (IRet None))
				      )
				      acc_ret	      
		      		      
				      
				  in
				  call_list,ret_list
			      )
			      
			      (try
				 (Hashtbl.find atoms (ICall (Some mod_repres.is_func.vname)))
			       with Not_found -> 
				 (Hashtbl.find atoms (ICall None))
			      )
			      (acc_c,acc_r)
			    )
			    (RState.Set.empty,RState.Set.empty)
			    mods_repres
			in
			
			
			addRStates call_set ref_current_mod;
			addRStates return_set ref_current_mod;
			Caret_option.debug ~dkey
			  "Call added : %i, Return added : %i"
			  (RState.Set.cardinal call_set)
			  (RState.Set.cardinal return_set);
			Stmt.Hashtbl.add 
			  stmt_call_ret_hashtbl 
			  stmt 
			  (call_set,return_set);
			
			doChildrenPostWithTrans ()
      		    end		
		(* Treated previously *)
	    | Info _ | CastE _ | Lval _ -> assert false
	      
	    | AddrOf _ | StartOf _ ->  
	      Caret_option.fatal 
		~dkey
		"Function pointers not supported"
	    | Const _ -> 
		  Caret_option.fatal 
		    ~dkey
		    "Calling a constant, interrupting."
		    
		| _ ->
		  Caret_option.fatal 
		    ~dkey
		    "Incorrect call, cannot be parsed as a box."
	      end
	    | Asm _ -> begin
	      Caret_option.debug ~dkey
		"ASM found, we don't treat it yet. Treated as a skip";
	      let cur_states = 
		mkRStateSetFromStmt 
		  ("ASM_" ^ string_of_stmt) 
		  stmt
		  kf
		  ref_current_mod
		  (Hashtbl.find atoms IInt)
	      in
	      addRStates cur_states ref_current_mod ;
	      
	      updateModStmtHashtbl ref_current_mod stmt cur_states;
	      doChildrenPostWithTrans ()
	    end

	    | Skip _ | Code_annot (_,_)  -> 
	      let () =  
		Caret_option.debug ~dkey ~level:2
		  "Statement is a Skip or an Annotation."
	      in
	      let cur_states = 
		mkRStateSetFromStmt 
		  ("SKIP_" ^ string_of_stmt) 
		  stmt
		  kf
		  ref_current_mod
		  (Hashtbl.find atoms IInt)
	      in 
	      
	      addRStates cur_states ref_current_mod; 
	      updateModStmtHashtbl ref_current_mod stmt cur_states;
              doChildrenPostWithTrans ()

	  in
	  match stmt.skind with
	    Instr i -> 
	      
	      begin
		try treatInstr stmt i
		with
		  
		  Func_not_found -> 
		    let () = 
		      Caret_option.feedback
			"The statement %s doesn't call any function, maybe a function pointer uninitialized."
			(Caret_print.string_stmt stmt);
		      updateModStmtHashtbl ref_current_mod stmt RState.Set.empty
		    in
		    
		    SkipChildren
		| e -> raise e
	      end
	  (* 
	     let cur_states = 
	     mkRStateSetFromStmt 
	     ("int_" ^ string_of_stmt) 
	     stmt
	     kf
			ref_current_mod
			(try 
			   Hashtbl.find atoms (ICall ))
		    in 
		    
		    addRStates cur_states ref_current_mod; 
		    updateModStmtHashtbl ref_current_mod stmt cur_states;
		    doChildrenPostWithTrans ()
		    *)
	  | Return _ -> 
	    let () =  
		Caret_option.debug ~dkey ~level:2
		  "Statement is a Return."
	    in
	    let cur_states = 
	      mkRStateSetFromStmt 
		("return_" ^ string_of_stmt) 
		stmt
		kf
		ref_current_mod
		(Hashtbl.find atoms IInt)
	    in
	    
	    let () = 
	      if isMainMod ref_current_mod
	      then
		let () = Caret_option.debug ~dkey "Adding self successor" in
		RState.Set.iter
		  (fun st -> st.s_succs <- RState.Set.add st st.s_succs; 
		    st.s_preds <- RState.Set.add st st.s_preds)
		  cur_states
	    in
	    
	    addRStates cur_states ref_current_mod;
	    updateModStmtHashtbl ref_current_mod stmt cur_states;
	    doChildrenPostWithTrans ()
	      
	      
	  | If (_ , _, _, _) -> 
	    (* For the reverse dataflow, we would like to use some information
	       about if_stmt. We will register it now. *)
	    (*let () = Rsm_dataflow.update_table stmt b1 b2
	    in*)
	    let () =  
		Caret_option.debug ~dkey:dkey_vis ~level:2
		  "Statement is an if."
	    in
	    let cur_states = 
	      mkRStateSetFromStmt 
		("cond_" ^ string_of_stmt) 
		stmt
		kf
		ref_current_mod
		(Hashtbl.find atoms IInt)
	    in 
	    
	    addRStates cur_states ref_current_mod; 
	    updateModStmtHashtbl ref_current_mod stmt cur_states;
            doChildrenPostWithTrans ()
	  | _ -> (* If not a call nor an if *)
	    let () =  
		Caret_option.debug ~dkey:dkey_vis ~level:2
		  "Statement is something."
	    in
	    let cur_states = 
	      mkRStateSetFromStmt 
		("int_" ^ string_of_stmt) 
		stmt
		kf
		ref_current_mod
		(Hashtbl.find atoms IInt)
	    in 
	    
	    addRStates cur_states ref_current_mod; 
	    updateModStmtHashtbl ref_current_mod stmt cur_states;
            doChildrenPostWithTrans ()
end  


let compute_rsm file formula closure atoms = 
 
  let () = compute_ignored_functions () in

  let rsm = mkEmptyRsm "main" in
  (*addUntils closure rsm; (* Adds for each General Until & Abstract Until
			    an empty list. *)
  *)

  let () = Caret_option.feedback "Creation of modules" in

  let visitor = rsm_create_modules rsm formula atoms in
  Cil.visitCilFile (visitor :> Cil.cilVisitor) file;

  let () = Caret_option.feedback "Creation of states" in
  
  let visitor = rsm_create_states closure atoms in 
  Cil.visitCilFile (visitor :> Cil.cilVisitor) file;

 (* Now we will treat the states that are in the todo set *)
  let () = Caret_option.feedback "Transitions" in
  begin

      List.iter
	(fun (a,b,c) -> 
	  try
	    createTransTo closure a b c
	      
	  with
	    Not_Treated_Prev _ ->
	      Caret_option.debug
		~dkey:dkey_vis
		"Statement --> \n%s \n <-- not registered."
		(Caret_print.string_stmt c)
	)
	!todo_states

  end;
  Caret_option.feedback "Buchi conditions creation";
  let () = 
    rsm.until_set <- Rsm.generateBuchi closure rsm in
  Rsm.addBuchiToRStates rsm ;

(*  let path_found =
    try 
      unfoldAutomaton rsm; None
    with
      Path_found e -> Some e*)

    

  rsm
