open Atoms
open Caret_option
open Rsmast
open Caretast
(* open Caret_visitor *)
(* open Rsm *)

open Type_RState
open Type_Box
open Type_Rsm_module

let dkey = Caret_option.register_category "main_caret" 
let output_fun chan = Printf.fprintf chan "%s\n" 

let treatment file formula closure atoms = 	    
  
  let () = (* Each fundec must be prepared *)
      let vis = 
        object
	  inherit Visitor.frama_c_inplace

	  method! vglob_aux g = 
	    match g with
	    | Cil_types.GFun (fundec,_) ->
	      Cfg.prepareCFG fundec; Cil.DoChildren
	    | _ -> Cil.DoChildren
	end 
      in
      Cil.visitCilFile (vis :> Cil.cilVisitor) file
  in
  (** Value computation *)
  let () = 
    
    let () = 
      Caret_option.feedback "Value computation";
      
	(*Dynamic.Parameter.Int.set "-slevel" 10*)  in
    !Db.Value.compute ()
  in
  let () = (* Checking if the main function ends or not *)
    let actually_ends = 
      Db.Value.is_reachable_stmt
	(Kernel_function.find_return 
	   (!Parameter_builder.find_kf_by_name "main"))
    in
    let user_says = Caret_option.Main_ends.get () 
    in
    
    if (not actually_ends) && user_says
    then 
      Caret_option.abort 
	"Your program never stops. If your program is supposed to end, then you should run Value (frama-c-gui \"your_file\".c -val. If it is not, run this plug-in with the option -caret-no-end."
    else
      if actually_ends && (not user_says)
      then
	let () = 
	  Caret_option.feedback 
	    "Your program eventually stops. Switching from -caret-no-end to -caret-end"
	in
	Caret_option.Main_ends.set true
  in
  Caret_option.feedback "Computing the automaton";
  Caret_option.feedback "Ignored functions : %s" 
    (List.fold_left 
    (fun acc f -> acc ^ "\n" ^ f) 
    "" 
    (Str.split (Str.regexp ";") (Caret_option.Ignore_fun.get ())));
  let rsm = 
    Caret_visitor.compute_rsm file formula closure atoms 
  in
  (** Different actions *)
  let cex = ref RState.Set.empty 
    (* The place where the counterexample is saved, if there is one *)
  in

  let () = 
    
    if Caret_option.Simplify.get () <> 0
    then 
      begin
	Caret_option.feedback "Starting the simplification";
	Rsm.simplifyAutomaton rsm;
	
      end 
  in


  (** Loop analysis  *)
  begin (* Acceptance *)
    
    if Create_res.get ()
    then
      let () = Caret_option.feedback "Acceptance analysis" in
      let () = 
	  Counter_example.testAcceptance rsm
      in
      if RState.Set.exists
	   (fun s -> 
	     match s.s_stmt.Cil_types.skind with
	       Cil_types.Return _ -> 
		 (not s.deleted)
	     | _ -> false)
	   rsm.start
      then 
	Caret_option.feedback "Every path has been deleted : no counter example found !"
      else 
	Caret_option.feedback "Cannot prove the formula."
       
  end; (* Acceptance *)

  begin (* Spurious *)
    if Spurious.get ()
    then
      output_fun stdout (Formula_utils.string_spurious ())
	
  end;(* Spurious *)
  
  begin (* Print automaton *)
    
    (** Printing the automaton  *)
    if not(Output_dot.is_default ())
    then 
      let file = Output_dot.get () in
      begin
        
	  let chan_dot = open_out file

	  in
	  
	  let rsm_str = 
	    
	    if Dot.get () 
	    then 
	      begin
		Caret_option.feedback
		  "Dot printing" ;
		
		Caret_print.string_rsm rsm ~cex:!cex
	      end
	    else
	      Caret_print.string_rsm_infos rsm ;
	    
	  in

	  output_fun chan_dot rsm_str;
	  close_out chan_dot
	    
	end
    end; (* Print automaton *)
    
    (** Getting states information  *)
    
    begin (* RState infos *)
      if not (Complete_states.is_default ())
      then
	    begin 
	      let chan_st = open_out (Complete_states.get ()) in 
	      output_fun 
		chan_st
		(Rsm_module.Set.fold
		   (fun r_mod str -> 
		     (RState.Set.fold 
			(fun state sub_str -> 
			  if not(Rsm.isDeleted state) then
			  let more_infos = 
			    match state.call with
			      Some (box,_) -> 
				"\nCalls the box :\n" ^ 
				  (box.b_name) ^ 
				  "_" ^ (string_of_int box.b_id) ^
				"\nAtomized by : " ^
				  (Caret_print.string_atom box.box_atom)
			    | None -> 
			      match state.return with
				Some(box,_) -> "\nCalls the box :\n" ^ 
				  (Caret_print.string_atom box.box_atom)
			      | None -> ""
			  in
			  sub_str ^ "\n\nRState :\n" 
			  ^ (Caret_print.simple_state state) 
			  ^ "\nAtom : " ^ (Caret_print.string_atom state.s_atom)
			  ^ (if Formula_datatype.Id_Formula.Set.is_empty state.s_accept
			    then ""
			    else "\nAccepts :" ^ Caret_print.string_raw_atom state.s_accept)
			  ^ more_infos
			  else ""
			)
			r_mod.states
			""
		     ) ^ 
		       (
			 Box.Set.fold 
			   (fun box sub_str -> 
			     "\nBox :\n"  
			     ^ (Caret_print.string_box box) ^ sub_str)
			   r_mod.box_repres
			   ""
		       ) ^ str 
		   )
		   rsm.rsm_mod
		   "\n");
	      close_out chan_st
	    end
    end (* RState infos *)
    
let work () = 
    (** Lexing & Parsing of the formula *)
  let fileform = Formula_file.get () in
  let chan_form = open_in fileform in

  let () = Caret_option.feedback ~dkey "Parsing the formula" in

  let lexbuf = Lexing.from_channel chan_form in
  let formula = Formula_parser.main Formula_lexer.token lexbuf in
  
  (** Computation of the closure / atoms from the formula *)
  let () = Caret_option.feedback ~dkey "Normalize" in
  let formula = Formula_utils.normalizeFormula formula in 
  Caret_option.feedback "Closure computation of the formula %s"
    (Caret_print.string_formula formula);  
  let formula = match formula with
      Caretast.CNot f -> f 
    | _ -> Caretast.CNot formula
  in
  let closure = Formula_utils.closure formula
  in
  
  Caret_option.feedback "Atoms computation";  
  let atoms = Hashtbl.create 12 in 
  let () = Formula_utils.mkAtoms closure atoms
  in
  
  
  begin (* Print closure *)
    if Closure.get () 
    then
      let () = 
	Caret_option.feedback
	  "Closure printing" in
      let closure_str = 
	List.fold_left
	  (fun acc form -> 
	    (Caret_print.string_formula 
	       (Formula_utils.getFormula form))  
	    ^ "\n" ^ acc)
	  "\n"
	  closure
      in
      let () = 
	Caret_option.feedback
	  "%s"
	  closure_str in
      if Output_closure.is_default () 
      then Caret_option.feedback "Closure file missing" 
	  (*output_fun stdout closure_str *)
      else  
	begin
	  Caret_option.feedback "Closure file here" ;
	  let filecl = Output_closure.get () in
	  let chan_cl = open_out filecl in
	  output_fun chan_cl closure_str;
	  close_out chan_cl
	end
  end; (* Print closure *)
  
    begin(* Print atoms *) 
    if Atoms.get () then
      begin
	Caret_option.feedback
	  "Atoms printing";
	
	let call,int,ret = 
	  Hashtbl.fold
	    (fun key bind (acc_call, acc_int, acc_ret) -> 
	      match key with
		ICall _ -> (Atom.Set.union bind acc_call, acc_int, acc_ret)
	      | IInt -> (acc_call, Atom.Set.union bind acc_int, acc_ret)
	      | IRet _ -> (acc_call, acc_int, Atom.Set.union bind acc_ret)
	    )
	    atoms
	    (Atom.Set.empty,Atom.Set.empty,Atom.Set.empty)
	in
	let atoms_str = 
	  (Atom.Set.fold
	     (fun atom acc -> Caret_print.string_atom atom  ^ "\n\n" ^ acc)
	     call
	     "\n\n"
	  ) ^
	    (Atom.Set.fold
	       (fun atom acc -> Caret_print.string_atom atom  ^ "\n\n" ^ acc)
	       int
	       "\n\n"
	    ) ^
	    (Atom.Set.fold
	       (fun atom acc -> Caret_print.string_atom atom  ^ "\n\n" ^ acc)
	       ret
	       "\n\n"
	    )
	in
	if Output_atoms.is_default ()  
	then () (* output_fun stdout atoms_str *)
    else  
      begin
	let fileat = Output_atoms.get () in
	let chan_at = open_out fileat in
	output_fun chan_at ((Caret_print.string_formula formula) ^ "\n\n");
	output_fun chan_at atoms_str;
	close_out chan_at
      end;
      end
    else ()
      
    end; (* Print atoms *)
    

    (** Slicing of the initial program *)
    (*let sliced_project = 
      begin
	let mark = !Db.Slicing.Mark.make ~data:false ~addr:true ~ctrl:true in
	let main_func = Globals.Functions.find_def_by_name "main" in
	
	let var_set = 
	  List.fold_left
	    (fun acc form -> 
	      match Formula_utils.getFormula form with 
		(Caretast.CProp (p,_)) ->  
		  Cil_datatype.Logic_var.Set.fold
		    (fun lvar acc2 -> match lvar.Cil_types.lv_origin with
		      Some vi -> Cil_datatype.Varinfo.Set.add vi acc2
		    | None -> acc2
		    )
		    (Cil.extract_free_logicvars_from_predicate p)
		    acc
	      | _ -> acc
	    )
	    Cil_datatype.Varinfo.Set.empty
	    closure
	in
	let () = 
	  Caret_option.feedback "%i variables to check" 
	    (Cil_datatype.Varinfo.Set.cardinal var_set)
	    
	in
	let slicing_parameter = 
	  Cil_datatype.Varinfo.Set.fold
	    (fun vi acc -> 
	      !Db.Slicing.Select.add_to_selects_internal
		(!Db.Slicing.Select.select_modified_output_zone_internal
		    main_func
	            (Locations.zone_of_varinfo vi)
		    mark	      
		)
		acc
	    )
	    var_set
	    Db.Slicing.Select.empty_selects
	in
	
	let new_slicing_project = !Db.Slicing.Project.mk_project "caret_slice" 
	in 

	let () = 
	  !Db.Slicing.Request.add_selection 
	    new_slicing_project 
	    slicing_parameter 
	in 
	
	let () = 
	  !Db.Slicing.Request.apply_all 
	    new_slicing_project 
	    ~propagate_to_callers:false
	in
	
	!Db.Slicing.Project.extract "caret_slice" new_slicing_project
      end
    in
    *)
    (** Computation of the automaton *)
    if Auto_gen.get () 
    then 
      begin
	Caret_option.feedback "Starting the preparation";
	let file = (Ast.get ()) in

	  Project.on 
	    (Project.current ())
	    (*sliced_project *)
	    treatment 
	    file 
	    formula 
	    closure 
	    atoms;
      end

let run () = 
  if Enabled.get () then

    let () = Caret_option.feedback "Begin"; 
    in
    
      
    let work_prj =
      File.create_project_from_visitor "caret_tmp"
	(fun prj -> new Visitor.frama_c_copy prj)
    in
    Project.copy ~selection:(Parameter_state.get_selection ()) work_prj;
    try
      Project.on work_prj work ();
    with
      Formula_utils.Unsatisfiable_formula -> 
	Caret_option.feedback "Formula is always valid";
    (*| Failure s -> Caret_option.abort "Failed by %s, need to be debugged." s*)
    Project.remove ~project:work_prj ()


let run =
  Dynamic.register
    ~plugin:"CaRet"
    "run"
    (Datatype.func Datatype.unit Datatype.unit)
    ~journalize:true
    run

let run, _ =
  State_builder.apply_once
    "CaRet"
    (let module O = Caret_option in
     [ O.Formula_file.self; O.Auto_gen.self; O.Create_res.self;
      O.Simplify.self; O.Output_dot.self; O.Dot.self;
      O.Output_closure.self; O.Closure.self;
      O.Output_atoms.self;O.Atoms.self;O.Complete_states.self;
      O.All_paths.self; O.Only_main.self ; O.Atom_simp.self])
    run

let () = Db.Main.extend run
