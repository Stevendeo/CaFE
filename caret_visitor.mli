open Rsmast
open Caretast
open Atoms

val mod_stmt_states_hashtbl :
  (((RState.Set.t) Cil_datatype.Stmt.Hashtbl.t) Rsm_module.Hashtbl.t)

val stmt_call_ret_hashtbl : 
  (RState.Set.t * RState.Set.t) Cil_datatype.Stmt.Hashtbl.t

val compute_rsm: 
  Cil_types.file -> caret_formula -> identified_formula list -> (atom_kind, Atom.Set.t) Hashtbl.t 
  -> rsm

(* 
val unroll_loops: Cil_types.file -> int -> unit
*)
