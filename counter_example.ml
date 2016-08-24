open Rsmast 
open Formula_datatype

type counter_example = (Ext_state.t list * Atoms.raw_atom) list * (((Ext_state.t list) * Id_Formula.Set.t) list)

exception Path_found of counter_example

let dkey = Caret_option.register_category "c_e" 

(* TODO : must check that the path in argument is not a spurious path *) 
let analyse_path path_list =
  
  List.length path_list >= 1

let add_result path loop_list res = 
  if Caret_option.All_paths.get() 
  then (path,loop_list)::res
  else 
    raise (Path_found (path,loop_list)) 

let analyse_loops _ paths_to_loop_head loop_head loop_paths_tbl = 
  let loop_paths = RState.Hashtbl.find loop_paths_tbl loop_head in
  
  List.fold_right
    (fun (path,acpt) acc -> 
      if List.length path = 1 then 
	add_result paths_to_loop_head [(path,acpt)] acc
      else 
	acc (* For now, only ending functions *)
    )
    loop_paths
    []

let search_paths rsm path_to_loop_tbl loops_tbl = 
  
  Caret_option.feedback
    "Search for counter example";
  
  let rsm_entries = rsm.start in 
  
  RState.Set.fold
    (fun entry acc -> 
      let () = 
	Caret_option.debug ~dkey 
	  "Entry %a"
	  RState.pretty entry in
      try
	let ending = RState.Hashtbl.find path_to_loop_tbl entry 
	in
	RState.Hashtbl.fold
	  (fun loop_entry path_list acc' -> 
	    let () = 
	      Caret_option.debug ~dkey 
		"linked to exit %a"
		RState.pretty loop_entry in

	    if analyse_path path_list then 
	      let loop_tbl = RState.Hashtbl.find loops_tbl loop_entry
	      in
	      analyse_loops rsm path_list loop_entry loop_tbl @ acc'
	    else acc')
	  ending
	  acc
      with 
	Not_found -> acc)
    rsm_entries
    []
    
    
    
