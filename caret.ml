open Atoms
open Caret_option
open Rsmast
open Caretast
open Formula_datatype
(* open Caret_visitor *)
(* open Rsm *)

open Type_RState
open Type_Rsm_module

let dkey = Caret_option.register_category "main_caret" 
let output_fun chan = Printf.fprintf chan

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
      let () = Counter_example.testAcceptance rsm
      in
      if not (Caret_option.Main_ends.get ())
      then
        let () =
          Caret_option.feedback
            "Program does not end, check the automaton (dot -Tpdf auto.dot > auto.pdf) to see if \
             there is accepting paths.";
          Caret_option.Output_dot.set "auto.dot" in
        Caret_option.Dot.set true
      else
      if RState.Set.exists
	   (fun s ->
	     match s.s_stmt.Cil_types.skind with
	       Cil_types.Return _ ->
		 (not s.deleted)
	     | _ -> false)
	   (Rsm.getMainMod rsm).states
      then
	Caret_option.feedback "Cannot prove the formula."
      else
	Caret_option.feedback "Every path has been deleted : no counter example found !"

  end; (* Acceptance *)

  begin (* Spurious *)
    if Spurious.get ()
    then
      output_fun stdout "%s" (Formula_utils.string_spurious ())
	
  end;(* Spurious *)
  
  begin (* Print automaton *)
    
    (** Printing the automaton  *)
    if not(Output_dot.is_default ())
    then 
      let file = Output_dot.get () in
      
      let chan_dot = open_out file
      in
      if Dot.get () 
      then 
        let () = 
          Caret_option.feedback
            "Dot printing" in
        Format.fprintf
          (Format.formatter_of_out_channel chan_dot)
          "%s"
	  (Caret_print.string_rsm rsm ~cex:!cex)
   
      else
        Format.fprintf (Format.formatter_of_out_channel chan_dot) "%a" 
          Caret_print.print_rsm_simple_info rsm ;
      
      close_out chan_dot
  end; (* Print automaton *)
    
    (** Getting states information  *)
    
    begin (* RState infos *)
      if not (Complete_states.is_default ())
      then
	    begin 
	      let chan_st = open_out (Complete_states.get ()) in 
              Format.fprintf (Format.formatter_of_out_channel chan_st)
                "%a"
                Caret_print.print_rsm_complete_state_info rsm;
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
  Caret_option.feedback "Closure computation of the formula %a"
    Caret_Formula.pretty formula;  
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
      if Output_closure.is_default () 
      then 
	Caret_option.feedback
	  "%a\n"
          (Format.pp_print_list 
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n") 
             Id_Formula.pretty) closure 
      else  
        let filecl = Output_closure.get () in
        let chan_cl = open_out filecl in
        let () = Format.fprintf 
                   (Format.formatter_of_out_channel chan_cl) 
                   "%a\n" 
                   (Format.pp_print_list  
                      ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n") 
                      Id_Formula.pretty) 
                   closure in
	close_out chan_cl
	
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
          let strfmt_atom_set  =  
	  (Atom.Set.iter
	     (fun atom -> Format.fprintf Format.str_formatter "%a\n\n" Atom.pretty atom)) in
          strfmt_atom_set call;
          strfmt_atom_set int;
          strfmt_atom_set ret;
          Format.flush_str_formatter ()
	in
        if Output_atoms.is_default ()  
        then () (* output_fun stdout atoms_str *)
        else  
      begin
	let fileat = Output_atoms.get () in
	let chan_at = open_out fileat in
        Format.fprintf 
          (Format.formatter_of_out_channel chan_at) "%a\n\n" Caret_Formula.pretty formula;
	output_fun chan_at "%s" atoms_str;
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
