open Rsmast
open Caretast
open Atoms
(** Prints simple informations about a statement *)
val string_stmt : Cil_types.stmt -> string

(** Prints the formula *)
val string_formula : caret_formula -> string

(** Prints the identified formula *)
val string_id_formula : identified_formula -> string

(** Prints a raw atom *)
val string_raw_atom : raw_atom -> string

(** Prints an atom *)
val string_atom : atom -> string

val simple_state : state -> string

val string_path : state list -> string

(** Returns the atomic properties verified within the state *)
val string_state_config : state -> string

val string_box : box -> string

(** Prints the rsm in argument (dot standard)  *)
val string_rsm : rsm -> string

(** Prints minimal informations about the automaton in argument.  *)
val string_rsm_infos : rsm -> string

(** Returns a string understandable by CVC from the predicate in argument *)
val pred_to_cvc : Cil_types.predicate -> string
