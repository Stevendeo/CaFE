open Caretast
open Formula_datatype
open Atoms_utils
open Atoms
open Rsmast
(* let dkey = Caret_option.register_category "printer" *)

open Type_RState
open Type_Box
open Type_Rsm_module

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

let string_formula formula = 
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
  let rec stringOf =  function
  
    | CNext (op,f) -> "( X"^ (printOpKind op) ^ (stringOf f) ^" )"
    | CUntil (op, f1 ,f2) -> 
      "( " ^(stringOf f1) ^ " U" ^(printOpKind op) ^ (stringOf f2) ^" )"
    | CFatally (op,f) -> "( F"^ (printOpKind op) ^ (stringOf f) ^" )"
    | CGlobally(op,f) -> "( G"^ (printOpKind op) ^ (stringOf f) ^" )"
    | CNot f -> "NOT\\(" ^  (stringOf f) ^ "\\)" (* Todo : delete the \ *)
    | CAnd (f1 ,f2) ->"( "^ (stringOf f1) ^ " & " ^ (stringOf f2) ^" )"
    | COr (f1, f2)-> "( "^ (stringOf f1) ^ " | " ^ (stringOf f2) ^" )"
    | CImplies (f1, f2)-> "( "^ (stringOf f1) ^ " => " ^ (stringOf f2) ^" )"
    | CIff (f1, f2)-> "( "^ (stringOf f1) ^ " <=> " ^ (stringOf f2) ^" )"  
    | CTrue -> "TRUE"
    | CFalse -> "FALSE"
    | CProp (_,str) -> str

    | CInfo i -> printInfo i
      
  in
  (stringOf formula)

let string_id_formula id_form = 
  "Formula n°"^ (string_of_int id_form.f_id) 
  ^ ": " ^ (string_formula id_form.form)

let stringAKind atom = match getAtomKind atom with
  | ICall (Some s) -> "Call_" ^ s ^ " - "
  | ICall _ -> "Call - "
  | IRet (Some s) -> "Ret_" ^ s ^" - "
  | IRet _ -> "Ret - "
  | IInt -> "Int - "

let string_raw_atom set = 
  if Id_Formula.Set.is_empty set then "[]" else
  Id_Formula.Set.fold
    (fun f acc ->
      (string_formula f.form)^ " ;\n " ^ acc
    )
    set
    "\n"   

let string_atom atom = stringAKind atom  ^ string_raw_atom (atom.atom)

let string_tag = function
  | Tag Inf | TagR -> "Inf"
  | Tag Fin -> "Fin"
  (* | IProp atom -> string_atom atom *)

(** 1. Rsm print  *)
(** RState printers *)

let short_state (state:state) = 
  deleteForbiddenDotChar 
    ((string_stmt state.s_stmt)^ (string_of_int state.s_id))

  
let string_state_set s_set = 
  RState.Set.fold
    (fun s a -> a ^"\n" ^ (short_state s))
    s_set
    "\n"

let simple_state state = 

  ("\"" ^ (short_state state) ^ "_st_" ^ (string_of_int state.s_id) ^(string_tag state.s_info)^ ": " ^ state.s_name (*^ link *) ^ "\"")

let string_path state_list = 
  List.fold_left (fun acc st ->acc ^ (simple_state st)(*(string_of_int st.s_id)*)  ^"\n" ) "" state_list

let string_state_config state = 
  let atom_props = atomicProps state.s_atom in
  "["^ String.trim (string_raw_atom atom_props) ^ "]"


let simple_box box = 
  "Box_" ^  box.b_name ^ (string_of_int box.b_id)

let string_box box = 
  
  (simple_box box)
  ^ "\nAtom : " ^ (string_atom box.box_atom)
  ^ "\n\nEntries :\n" 
  ^ RState.Map.fold 
    (fun call ent acc -> 
      acc ^ (simple_state call) 
      ^ "->" ^ (string_state_set ent) ^ "\n")
    box.b_entries
    ""
  ^ "\nExits :\n"
  ^ RState.Map.fold 
    (fun ext ret acc -> 
      acc ^ (simple_state ext) 
      ^ "->" ^ (string_state_set ret) ^ "\n")
    box.b_exits
    ""

let string_state rsm ?(cex = RState.Set.empty) ?(boxes = ref Box.Set.empty) state = 
(* Replace "short_state" by "simple_state" for a complete graph but be
   careful, you also need to change the name used for the transitions ! *)

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
    
let string_acceptance rsm = 

    Id_Formula.Set.fold
      (fun f acc -> 
	acc ^ (string_formula f.form) ^ "\n"
      )
      rsm.until_set 
      "Conditions : \nInf\n"
  
   
let string_rsm_infos rsm = 
  let total_trans = ref 0 in 
  let string_mod_info r_mod =
    let mod_trans = 
      RState.Set.fold
	(fun state acc -> acc + RState.Set.cardinal state.s_succs)
	r_mod.states
	0
      in
    let () = total_trans := mod_trans + !total_trans in
    "\nModule " ^ r_mod.mod_name ^ " :\n "
    ^(string_of_int(RState.Set.cardinal r_mod.entries)) ^" entries\n "
    ^(string_of_int(RState.Set.cardinal r_mod.exits)) ^" exits\n "
    ^(string_of_int(RState.Set.cardinal r_mod.states)) ^" states\n "
    ^(string_of_int(mod_trans)) ^ " transitions / plugs"
  in
  let number_state,str_mod_info = 
    Rsm_module.Set.fold
      (fun r_mod (st,str) -> 
	(st + (RState.Set.cardinal r_mod.states),
	 str  ^ (string_mod_info r_mod) ^ "\n--"))
      rsm.rsm_mod
      (0,"")
      
  in
  let starts = 
    RState.Set.fold
      (fun start acc -> (simple_state start) ^"\n" ^ acc)
      rsm.start
      ""
  in
  "Number of states :" ^ string_of_int number_state ^ 
    "\nNumber of trans : " ^ string_of_int !total_trans  ^
    "\nStarts : "  ^ starts 
  ^ "\nAcceptance sets :\n" ^  string_acceptance rsm  ^ "\n"
  ^ str_mod_info

let pred_to_cvc _ = ""
