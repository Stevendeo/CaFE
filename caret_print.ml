open Atoms
open Formula_datatype
open Rsmast
(* let dkey = Caret_option.register_category "printer" *)

open Type_RState
open Type_Box
open Type_Rsm_module


let print_rsm_complete_state_info fmt rsm = 

  let print_state_info_caller fmt s = 
    match s.call with
      Some (box,_) -> 
        Format.fprintf fmt "Calls the box %a\nAtomized by %a"
          Box.pretty box
          Atom.pretty box.box_atom
    | None -> 
      match s.return with
	Some(box,_) -> 
          Format.fprintf fmt  "Returns from the box :%a\n"
            Box.pretty box
      | _ -> ()
  in
  let print_state fmt s = 
    Format.fprintf fmt
      "State %a\nAtom: %a\n%s%a\n%a\n\n"
      RState.pretty s
      Atom.pretty s.s_atom
      (if Id_Formula.Set.is_empty s.s_accept then "" else "Accepts:\n")
      Atoms.pretty_raw_atom s.s_accept
      print_state_info_caller s      
  in
  
  Rsm_module.Set.iter
    (fun rmod -> 
       Format.fprintf fmt "Module %a:\n" Rsm_module.pretty rmod;
       RState.Set.iter
         (fun state -> 
            Format.fprintf fmt "%a\n" print_state state)
         rmod.states)
    rsm.rsm_mod


let print_rsm_simple_info fmt rsm = 
  let total_trans = ref 0 in 
  let print_mod_info r_mod =
    let mod_trans = 
      RState.Set.fold
	(fun state acc -> acc + RState.Set.cardinal state.s_succs)
	r_mod.states
	0
      in
      let () = total_trans := mod_trans + !total_trans in
      Format.fprintf fmt "Module %s:\n%d entries\n%d exits\n%d states\n%d transitions/plugs\n\n"
        r_mod.mod_name
        (RState.Set.cardinal r_mod.entries)
        (RState.Set.cardinal r_mod.exits)
        (RState.Set.cardinal r_mod.states)
        mod_trans
  in
  let number_state = 
    Rsm_module.Set.fold
      (fun r_mod st -> 
         print_mod_info r_mod;
	 (st + (RState.Set.cardinal r_mod.states)))
    rsm.rsm_mod
    0
      
  in

  Format.fprintf fmt
    "Number of states: %d\n\
     Number of trans:  %d\n\
     Starts : \n%a\n\
     Acceptance sets:\n Inf\n%a\n"
    number_state 
    !total_trans 
    RState.pretty_state_set rsm.start 
    Atoms.pretty_raw_atom rsm.until_set



let deleteForbiddenDotChar str = 
  let isForb = function
    | ':' | '|' | '"' -> true
    | _ -> false
  in
  String.map
    (fun c -> if isForb c then ' ' else c) str

let string_stmt (stmt:Cil_types.stmt) = 
 
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


let print_path fmt s_list = 
  Format.fprintf fmt "%a"
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n") RState.pretty) s_list

  (* | IProp atom -> string_atom atom *)

(** 1. Rsm print  *)
(** RState printers *)

let short_state (state:state) = 
  deleteForbiddenDotChar 
    ((string_stmt state.s_stmt)^ (string_of_int state.s_id))

let simple_box box = 
  "Box_" ^  box.b_name ^ (string_of_int box.b_id)

let string_state rsm ?(cex = RState.Set.empty) ?(boxes = ref Box.Set.empty) state = 

  let color = 
    if RState.Set.mem state cex
    then ", color=red"
    else ""
  in


  let id = string_of_int state.s_id in
  match state.call with
    Some (box, _) -> 
      if not (Box.Set.mem box !boxes )
      then
	begin
	  boxes := Box.Set.add box !boxes ;
	  
	  (simple_box box) ^ " [shape=box]\n"
	^ id ^  "[label = \"" ^ (short_state state)  ^  "\",shape = rarrow];\n"
	end      
      else
	id ^  "[label = \"" ^ (short_state state)  ^  "\",shape =  rarrow ];\n"
  | None -> match state.return with
    Some (box, _) ->

      if not (Box.Set.mem box !boxes)
      then
	begin
	  boxes := Box.Set.add box !boxes;
	  (simple_box box) ^ " [shape=box]\n"
	  ^ id ^  "[label = \"" ^ (short_state state)  
	  ^ "\",shape = larrow];\n"
	end
      else 
	id ^  "[label = \"" ^ (short_state state)  ^  "\",shape = larrow ];\n"
    | None -> 
      let shape = 
	let card = Id_Formula.Set.cardinal state.s_accept in 
	if card = 0 then "octagon" 
	else if (Id_Formula.Set.cardinal rsm.until_set) = card
	then "tripleoctagon"
	else "doubleoctagon" in
      id ^  
	"[label = \"" ^ (short_state state)  ^  "\",shape = " ^ shape ^ color ^" ];\n"

let string_state_set rsm ?(cex = RState.Set.empty) s_set = 
  
  RState.Set.fold
    (fun st acc -> acc ^ (string_state rsm ~cex st) )
    s_set
    ""

(** Transition printers  *)

let string_trans_from_end end_state =
  let id = string_of_int end_state.s_id in
  let trans_preds = 
    RState.Set.fold 
     (fun pred acc -> 
	 acc ^ (string_of_int pred.s_id) ^ " -> " ^ id ^ ";\n"
     )
      end_state.s_preds
      ""
  in
  let trans_preds = 
    RState.Set.fold
      (fun pred acc ->  
	acc 
	^ (string_of_int pred.s_id) 
	^ " -> " 
	^ id 
	^ " [style = dashed];\n"
      )
      end_state.summary_preds
      trans_preds
  in
  begin

  if end_state.call <> None 

  then 
    let box = fst (Extlib.the end_state.call) in

    (trans_preds ^ id ^ " -> " ^
       (simple_box box) ^ "\n")
	
  else 
    if end_state.return <> None
    then 
      let box = fst (Extlib.the end_state.return) in
          (trans_preds ^ (simple_box box)  ^ " -> " ^ id ^ "\n")

    else
      trans_preds
 end
let string_tr_set_of_mod r_mod  = 
  
  RState.Set.fold
    (fun state acc -> acc ^ (string_trans_from_end state))
    r_mod.states
    ""

(** Automaton printers  *)

let string_rank r_mod = 
  
  let rec split_states states = 
    if RState.Set.is_empty states 
    then ""
    else 
      let rand_state = RState.Set.choose states in
      let is_call = rand_state.call <> None in
      let is_ret = rand_state.return <> None in
      let same,diff = 
	RState.Set.partition
	  (fun st -> 
	    Cil_datatype.Stmt.equal st.s_stmt rand_state.s_stmt
	    && (not(is_call) || st.call <> None)
	    && (not(is_ret) || st.return <> None)
	  )
	  states
      in
      (RState.Set.fold
	 (fun st acc ->  acc ^ " " ^ (string_of_int st.s_id))
	 same
	 "{rank = same")
      ^ "}\n"
      ^ (split_states diff)
  in
  split_states r_mod.states
  
let string_module rsm ?(cex = RState.Set.empty) r_mod = 
 "subgraph clustermod_" ^ (string_of_int r_mod.mid) 
  ^ "{\nlabel = \"" ^  r_mod.mod_name ^ "\";\n" ^ 
  (string_state_set rsm ~cex
     (RState.Set.filter (fun s -> (not s.deleted)) r_mod.states) )
  ^ "\n\n"
  ^ (string_tr_set_of_mod r_mod) ^ "\n"
  ^ string_rank r_mod 
  ^ "}"
  
  
    
let string_rsm ?(cex = RState.Set.empty ) rsm = 
  "digraph " ^ rsm.name  ^ " {\nsplines=ortho\n"  
  ^ (Rsm_module.Set.fold
       (fun r_mod acc -> (string_module rsm ~cex r_mod) ^ acc)
       rsm.rsm_mod)
       ""
  ^ "}\n"
  
