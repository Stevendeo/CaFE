open Cil_datatype
open Cil_types
open Zipper
open Rsmast 
open Formula_datatype
open Caretast

open Type_RState
open Type_Rsm_module
open Ext_state
exception Path_found of 
    Ext_state.t list * (((Ext_state.t list) * Id_Formula.Set.t) list)

(*type real_system = Sys_end | Sys_state of stmt * Db.Value.state

exception Bad_counterexample*)

let dkey = Caret_option.register_category "counter_example:ceana"
let dkey_reg = Caret_option.register_category "counter_example:regist" 
(*let mod_stmt_states_hashtbl = Caret_visitor.mod_stmt_states_hashtbl

let stmt_call_ret_hashtbl = Caret_visitor.stmt_call_ret_hashtbl

(*let loop_stack = ref Stmt.Stack.empty*)*)

let (real_system: ((Db.Value.state zipper) Stmt.Hashtbl.t)) = 
  Stmt.Hashtbl.create 42

let main () = Globals.Functions.find_by_name "main"


(* This hashtbl is filled during "isConsistent" called in the visitor. *)
(*let (spurious_stmt_hashtbl: Id_Formula.Set.t Cil_datatype.Stmt.Hashtbl.t)
    = Formula_utils.spurious_stmt_hashtbl
*)
let registerValuesLoop (stmt,_,s_list) = 

  Caret_option.debug ~dkey:dkey_reg "@[%a@] being studied" Printer.pp_stmt stmt;
      try
	begin 
	  let joined_s_list = 
	    let res_opt = 
	      List.fold_left
		(fun acc state -> 
		  match acc with 
		    None -> Some state
		  | Some acc -> Some (Cvalue.Model.join acc state)
	    )
		None
		s_list
	    in
	    match res_opt with
	      None -> raise (Failure "registering")
	    | Some s -> 
	      let () = 
		Caret_option.debug ~dkey:dkey_reg 
		  "Registering @[%a@]" 
		  Db.Value.pretty_state s
	      in
	      s
	  in
      let old_bind = 
	try 
	  Stmt.Hashtbl.find real_system stmt
	with
	  Not_found -> Zipper.empty
      in
      
      Stmt.Hashtbl.replace 
	real_system 
	stmt 
	(Zipper.insert old_bind joined_s_list)
	end
      with
	Failure "registering" -> 
	  Caret_option.debug ~dkey:dkey_reg "Failed to being registered"

let printValueResults () = 
  Stmt.Hashtbl.iter
    (fun stmt zip ->
      
      Caret_option.feedback
	"Before statement @[%a@], we have :\n" Printer.pp_stmt stmt ;
      
      Zipper.iter
	(fun state -> 
	  Caret_option.feedback "@[%a@]\n" Db.Value.pretty_state state
	)
        zip
	
    )
    real_system

let reseted = ref false

(* Expensive, use with caution *)
let resetAllZippers () = 
  if !reseted then () else let () = reseted := true in

  Stmt.Hashtbl.iter 
    (fun k b -> Stmt.Hashtbl.replace real_system k (Zipper.reset_left b))
    real_system

let resetOneStepZippers path edge = 
  Caret_option.debug ~dkey ~level:3 
    "Reseting path %s" (Caret_print.string_path (List.map to_state path));
  try List.iter 
    (fun est ->
      try 
	match est with 
	  State st ->
	    if st.return <> None then () else
	      let () = Caret_option.debug ~dkey ~level:3 
		"Reseting %s" st.s_name in
		let old_bind = Stmt.Hashtbl.find real_system st.s_stmt in
		Stmt.Hashtbl.replace real_system st.s_stmt 
		  (Zipper.move_left old_bind);
		if RState.equal st edge 
		then failwith "stop" ; ()
     
	| _ -> ()
     with
      | Invalid_argument "move_left" -> 
	Caret_option.debug ~dkey ~level:3 
	  "Nothing to reset here !")
    path
  with Failure "stop" -> ()

let getAndMove stmt = 
  reseted := false;
  try 
    let z = Stmt.Hashtbl.find real_system stmt in
    let () = 
      Stmt.Hashtbl.replace real_system stmt (Zipper.move_right z)
    in
    get_right z
      
  with
    Not_found (* Hashtbl.find *) -> 
      let () = 
	Caret_option.debug ~dkey 
	  "Statement @[%a@] not found in the value results"
	  Printer.pp_stmt stmt
      in raise Not_found
  | Invalid_argument "move_right" ->
    let z = Stmt.Hashtbl.find real_system stmt in
    let prev_state = get_left z in
    let () = 
      Caret_option.debug ~dkey
	"Statement @[%a@] has reached a fix_point." 
	Printer.pp_stmt stmt 
	;
      Caret_option.debug ~dkey
	 "@[%a@]" 
	Db.Value.pretty_state prev_state
    in
    prev_state
    

type cegar_ret = 
  Ok of Id_Formula.Set.t * Db.Value.state 
| Spurious of Ext_state.t * Db.Value.state

let testConsistency state atom = 
  
  let eval_to_bool = 
    let open Property_status in (* A module from the plugin Value *)
    function
    | True | Dont_know -> true 
    | False_if_reachable | False_and_reachable  -> false
  in

  let eval_pred state pred = 
    
      !Db.Value.Logic.eval_predicate 
	  (Db.Value.get_initial_state (main ())) 
	  state 
	  pred
      
  in

  let treatForm f =
    let form = Formula_utils.getFormula f in
    let () = Caret_option.debug ~dkey ~level:1 
      "Is @[%a@] consistent with %s ?"
      Db.Value.pretty_state state
      (Caret_print.string_formula form)
    in
    match form with
      CProp (pred,_) -> 
	eval_to_bool (eval_pred state pred)

    | CNot (CProp (pred,_)) -> 
      let prop_stat = 
	eval_pred state pred
      in  	  
      
      prop_stat <> Property_status.True

    | _ -> true

  in
  let res = 
  Id_Formula.Set.for_all 
    treatForm
    (Atoms_utils.getPropsFromAtom atom)
  in
  Caret_option.debug ~dkey ~level:1 "%b" res; res


let cegar_path 
    ?(init = None) ?(acpt = Id_Formula.Set.empty) (path:Ext_state.t list) = 

  let open Ext_state in

  let end_state = ref init in
  let in_loop = ref [] in

  let () = Caret_option.debug ~dkey ~level:1
    "Analysing the path %s"
    (Caret_print.string_path (List.map to_state path)) in
  
  let rec throughPath ?(cond = None) acpt = function 
    | [] -> (Ok (acpt,(Extlib.the !end_state)))
    | State hd :: tl ->
      
      let acpt = Id_Formula.Set.union hd.s_accept acpt in
      
      if hd.return <> None 
      (* Already treated in the previous state, the call *)
      then throughPath ~cond acpt tl else
	begin (* hd.return = None *)
      Caret_option.debug ~dkey "Treatment of statement @[%a@] at the state with id %i"  
	Printer.pp_stmt hd.s_stmt
	hd.s_id;
	  
      let hd_state = getAndMove hd.s_stmt in
      if not(testConsistency hd_state hd.s_atom)
      then
	let () = Caret_option.debug ~dkey "Inconsistent !"
	in
	let () = resetOneStepZippers path hd in
	Spurious ((State hd),hd_state)
      else
      let () = end_state := (Some hd_state);

	Caret_option.debug ~dkey "with state @[%a@]"
	  Db.Value.pretty_state hd_state
	
      in
      let () = match hd.s_stmt.skind with 
	  Loop _ -> 
	    begin
	      try
		if not(Stmt.equal hd.s_stmt (List.hd !in_loop))
		  
		then
		  in_loop := (hd.s_stmt) :: !in_loop 
	      with Failure "hd" -> in_loop := (hd.s_stmt) :: !in_loop 
	    end
	| Break _ -> begin try in_loop := List.tl !in_loop with _ -> () end
	  
	| _ -> ()
      in
      if 
(*	  not(Stmt.Hashtbl.mem spurious_stmt_hashtbl hd.s_stmt) 
	||*) (List.length hd.s_stmt.succs) <= 1
      then 
	throughPath ~cond acpt tl
      else (* Possibly spurious and more than one successor *)
	let fstStmt blk = match blk.bstmts with
	    [] -> Cil.dummyStmt
	  | fst::_ -> fst
	in
	
	let next = 
	  match 
	    begin try (List.hd tl) with Failure _ -> List.hd path end
	  with
	    State s -> s
	  | _ -> assert false
	in
	let () = 
	  Caret_option.debug ~dkey 
	    "Is @[%a@] the right successor ?" 
	    Printer.pp_stmt 
	    next.s_stmt; 
	in
	
	let with_alarms = CilE.warn_none_mode in

	(* Some true -> then
	   Some false -> else
	   None -> Don't know*)
	let then_or_else = ref None in
        let is_spur = 
	  match hd.s_stmt.skind with
	    If(e,b1,_,_) -> 
		let c_res = 
		  !Db.Value.eval_expr 
		    ~with_alarms
		    hd_state
		    e 
		in
		if 
		(Ival.is_one (Cvalue.V.project_ival c_res))
		then 
		  let () = Caret_option.debug ~dkey 
		    "The then part has been taken during the analysis"; 
		    then_or_else := (Some true)
		  in 
		  not(Stmt.equal (fstStmt b1) (next.s_stmt))
		else if (Ival.is_zero (Cvalue.V.project_ival c_res))
		then
		  let () = Caret_option.debug ~dkey 
		    "The else part has been taken during the analysis";
		    then_or_else:= (Some false) in 
		  
		  Stmt.equal (fstStmt b1) (next.s_stmt) 
		else
		  let () = Caret_option.debug ~dkey 
		    "We can go both paths." ;
		    then_or_else := None
		  in
		  false
		  
	  | _ -> Caret_option.fatal 
	      "No such thing than a statement with multiple successors that is not an \"if\" !"
	in
	
	  if is_spur 
	  then 
	    if !in_loop = []
	    then 
	      let () = 
		Caret_option.debug ~dkey 
		   "Spurious, as we are not in a loop";
		resetOneStepZippers path hd  in   
	      
	      Spurious ((State hd),hd_state)
	    else
	      
	    let () = 
	    Caret_option.debug ~dkey 
	      "Spurious ?" in
	    let rec f_until_g f g zip cpt = try
	      if not(f (Zipper.get_right zip)) then (zip,-1)
	      else if (g (Zipper.get_right zip)) then
		((Zipper.move_right zip),cpt)
	      else f_until_g f g (Zipper.move_right zip) (cpt + 1)
	      with _ -> (zip,-1)
	    in
	    let zip_out_loop,cpt = 
	      let zip = Stmt.Hashtbl.find real_system hd.s_stmt
	      in 
	      let f state = 
		testConsistency state next.s_atom
	      in
	      let exp = 
		match hd.s_stmt.skind with
		  If(e,_,_,_) -> e | _ -> assert false
	      in
	      let g state = 
		let c_res = 
		  !Db.Value.eval_expr 
		    ~with_alarms
		    state
		    exp
		in
		let () = Caret_option.debug ~dkey 
		  "c_res = @[%a@]" Db.Value.pretty c_res in
		let cont_zero = (Cvalue.V.contains_zero c_res)
		in

		match !then_or_else with
		  Some false -> not cont_zero
		| Some true -> cont_zero
		| None -> cont_zero && (Cvalue.V.contains_non_zero c_res)
	      in 
	      f_until_g f g zip 0
		
	    in
	    if cpt = -1 then 
	      let () = 
		Caret_option.debug ~dkey 
		  "Spurious, as we cannot take enough loop steps";
		resetOneStepZippers path hd
	      in   
	      
	      Spurious ((State hd),hd_state)
	    else
	      let () = 
		Stmt.Hashtbl.replace real_system hd.s_stmt zip_out_loop;
		Caret_option.debug ~dkey 
		  "Not yet"
	      in 
	      throughPath ~cond acpt tl
	      
	  else throughPath ~cond acpt tl
	    (* todo : propagate the information on getting in an "then" path
	       or an "else" path*)
	end (* hd.return = None *)
    | Summary paths :: tl -> 
      (* TODO : apply ceana path on summay paths *)
      let acpt = List.fold_left
	(fun acc (_,a) -> Id_Formula.Set.union a acc)
	acpt
	paths in
      throughPath ~cond acpt tl 
  in
  throughPath acpt path

let cegar_loop init loop = 
    match cegar_path ~init:(Some init) loop with
      Ok _ as res -> 
	let () = 
	  Caret_option.debug ~dkey 
	    "We can get through" 
	in
	res
	  
    | Spurious ((State hd),hd_state) as s -> 
      Caret_option.debug ~dkey 
	"@[%a@] with state @[%a@] has the wrong successor." 
	Printer.pp_stmt hd.s_stmt
	Db.Value.pretty_state hd_state; s
    | Spurious ((Summary _),_) -> assert false
(*
let is_spurious (path,loop_list) = 

  let rec cegar_loops possible_states init loops = 
    
    match loops with 
      loop :: tl ->  begin  (* loop :: tl *)
	let res = cegar_loop init loop in 
	match res with
	  Ok _ -> false
	| Spurious (st, val_st) -> 
	  match st.s_stmt.skind with 
	    Loop _ -> 
		  (* We went through the loop but we didn't end in the 
		     right state,
		     we will have to unfold the loop one more time. *)
	      let () = Caret_option.debug ~dkey 
		"Possibly spurious loop. New state : @[%a@]" 
		Db.Value.pretty_state val_st in 
	      cegar_loops (val_st::possible_states) val_st tl
		
		
	  | _ -> (* this path was bad *) 
	    cegar_loops possible_states init tl
      end (* loop :: tl *)
    | [] -> 
	  (* we called cegar_loops on all the loops *)
      if possible_states = [] then true else 
	List.for_all (fun init -> cegar_loops [] init loop_list) possible_states
	  
  in
  
  
  if not(Caret_option.Cegar.get ()) then false else
    let () = 
      Caret_option.debug ~dkey 
	"Counter example is \n Path ->\n %s\n Loops :\n %s"
	(Caret_print.string_path (List.rev path))
	(List.fold_left 
	   (fun acc loop -> 
	     "\n ->" ^ (Caret_print.string_path loop) ^ acc) 
	   "" 
	   loop_list);
      resetAllZippers () in
    match cegar_path (List.tl (List.rev path)) with 
      Spurious _ -> true
    | Ok s -> 
      cegar_loops [] s loop_list
*)

let analyse_paths rsm path_to_loop_tbl loop_tbl = 
  let () = Caret_option.debug ~dkey "Counter example research" in
  (* acpt_acc keeps in memory the acceptance condition crossed in 
     validated loops*)
  let () = resetAllZippers () in
  let rec cegar_loops 
      loop_head acpt_acc possible_states init loops kept_loops = 
    if not (Caret_option.Ceana.get ()) then true 
    else
    match loops with 
      (loop,acpt) :: tl ->  begin  (* loop :: tl *)
	let res = cegar_loop init loop in 
	match res with
	  
	  Ok (a,s) ->
	    if Cvalue.Model.is_included s init
	    (* Then we can take this path an infinite number of time : we can
	       stop analysing this loop. *)
	    (* Todo : is it here we stop the analysis, having found a 
	       nice loop ? *)
	    then 
	    (*let () = if tl <> [] then resetOneStepZippers loop loop_head 
	    in*)
	      cegar_loops loop_head
		(Id_Formula.Set.union a acpt_acc)
		(s :: possible_states)
		init 
		tl
		kept_loops
		 
	    else
	      let () = Caret_option.debug ~dkey 
		"Possibly spurious loop, not included in @[%a@]. New state : @[%a@]" 
		Db.Value.pretty_state init
		Db.Value.pretty_state s
	      in
	      cegar_loops loop_head
	        acpt_acc
		(s :: possible_states)
		init 
		tl
		((loop,acpt) :: kept_loops)
		
	| Spurious _ -> 
	  let () = Caret_option.debug ~dkey 
	    "Taking this loop with the state @[%a@] is impossible."
	    Db.Value.pretty_state init
	  in
	  cegar_loops loop_head
	    acpt_acc
	    possible_states 
	    init
	    tl
	    ((loop,acpt) :: kept_loops)
	    
	    
      end (* loop :: tl *)
    | [] -> 
      (* we called cegar_loops on all the loops *)
      if possible_states = [] then false
      else
	if Id_Formula.Set.cardinal acpt_acc = 
	  Id_Formula.Set.cardinal rsm.until_set
	then true 
	else
	  List.exists 
	    (fun init -> 
	      cegar_loops loop_head
		Id_Formula.Set.empty 
		[] 
		init 
		kept_loops
		[]
	    )
	    possible_states
	    
  in
  let can_be_accepting paths = 
    let total_acpt = 
      List.fold_left 
	(fun acc (loop,_) -> 
	  List.fold_left 
	    (fun acc2 -> function
	    | State s -> Id_Formula.Set.union s.s_accept acc2
	    | Summary sum_list -> 
	      List.fold_left 
		(fun acc3 (_,a) ->  
		  Id_Formula.Set.union a acc3)
		acc2
		sum_list)
	    acc
	    loop
	)
	Id_Formula.Set.empty
        paths
    in
    Id_Formula.Set.cardinal total_acpt 
    = Id_Formula.Set.cardinal rsm.until_set
	
  in
  RState.Hashtbl.iter
    (fun entry loop_head_tbl ->
      if not(entry.s_mod.is_func.Cil_types.vorig_name = "main") 
	|| not (
	  RState.Set.is_empty entry.s_preds
	  && not(entry.return <> None)) (* isRet *)
      then 
	()
      else
	  RState.Hashtbl.iter
	    (fun loop_head paths_to_loop_head ->
	      if not(RState.Hashtbl.mem loop_tbl loop_head)
	      then
	        ()
	      else
		(* RState.Hashtbl.mem loop_tbl loop_head *)
		
		
		let paths_ok = 
		  List.fold_left
		    (fun acc (path,_) ->
		      let () = 
			Caret_option.debug ~dkey
			  "Path treated : %s"
			  (Caret_print.string_path (List.map to_state path))
		      in
		      
		      
		      if path = [] 
		      then (* The path is direct from the entry to the loop *)
			try 
			  let s = getAndMove loop_head.s_stmt in

			  (s,path) :: acc 
			    
			with
			  Not_found (* hashtbl.find *)-> 
			    let () =  
			      Caret_option.debug ~dkey 
				"Stmt @[%a@] not treated by value"
				Printer.pp_stmt loop_head.s_stmt;
			    in acc
			| Failure "get_right" -> 
			  assert false
		      else (* path <> [] *)
			let last_state = 
			  path 
			|> List.rev 
			|> List.hd 
			|> Ext_state.to_state
			in
			let is_ls_a_ret = 
			  match last_state.s_stmt.skind with
			    Return _ -> true
			  | _ -> false
			in
			if 
			  ((
			    (
			      (Caret_option.Main_ends.get ()) 
			      && (not is_ls_a_ret)
			    )
			   )
			   || 
			     (
			       (not (Caret_option.Main_ends.get ()) 
				&& is_ls_a_ret)
			     ))
			    
			then (* path is not correct *)
			  acc
			else if not (Caret_option.Ceana.get ()) 
			then (* No ceana *)
			  (getAndMove loop_head.s_stmt,path)::acc
			else (* Ceana *)
			  
			  match cegar_path path with
			    
			    Spurious _ -> 
			      acc
			  | Ok (_,s) -> 

			      if 
				(Caret_option.Main_ends.get ())
				&& is_ls_a_ret 
				&& (Id_Formula.Set.cardinal 
				      (last_state).s_accept
				    = Id_Formula.Set.cardinal rsm.until_set)
			      then raise (Path_found (path,[]))
			      else 
				(s,path) :: acc
		    )
		    []
		    paths_to_loop_head
		in
		let () = 
		    (List.iter
		       (fun (s,path) -> 
			 Caret_option.debug ~dkey "Path accepted : \nState = @[%a@]\n Path =  %s\n\n"
			   Db.Value.pretty_state s
			   (Caret_print.string_path 
			      (List.map to_state path))
		       )
		       
		       paths_ok
		    )
		in
		let treated_states = ref [] in
		(* We save here the Value states
		   already treated *)
		
		let loops = 
		  RState.Hashtbl.find
		    (RState.Hashtbl.find loop_tbl loop_head)
		    loop_head
		in
		let () = Caret_option.debug ~dkey
		  "Loop to treat :%s "
		  
		     (List.fold_left
			(fun acc (loop,_) -> 
			  let acpt = 
			    List.fold_left 
			      (fun acc2 st -> match st with
				| State s -> 
				  Id_Formula.Set.union s.s_accept acc2
				| Summary sum_list -> 
				  List.fold_left 
				    (fun acc3 (_,a) ->  
				      Id_Formula.Set.union a acc3)
				    acc2
				    sum_list)
			      
			      Id_Formula.Set.empty
			      loop
			
			  in
			  acc ^ "\n_____________\nAccepting " ^ 
			    (Caret_print.string_raw_atom acpt)
			  ^ "\n"
			  ^ (Caret_print.string_path 
			       (List.map to_state loop)))
		     
			""
			loops
		    
		  )		     
		       
		in
		

		if not(can_be_accepting loops)
		then
		  ()
		else
		    List.iter
		    (fun (s,path) -> 
		      if List.mem s !treated_states
		      then ()
		      else 
			let () = Caret_option.debug ~dkey ~level:3 
			  "Path analysed : %s"
			  (Caret_print.string_path
			     (List.map Ext_state.to_state path))
			in
			let () = treated_states := s :: !treated_states 
			in
			if (not(Caret_option.Ceana.get ())) 
			then
			  let () = 
			    Caret_option.feedback
			      "Ceana not active"
			  in
			  raise (Path_found (path,loops))
			else
			  
			  let () = 
			    Caret_option.feedback
			      "Ceana is active"
			  in
			  if  (
			    cegar_loops  loop_head
			      Id_Formula.Set.empty
			      [] 
			      s 
			      loops
			      [])
			  then
		            raise (Path_found (path,loops))
			  else
			    ()
		    )
		      
		    paths_ok
		    
	    )
	    
	    loop_head_tbl
    )
    path_to_loop_tbl

