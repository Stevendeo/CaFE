open Rsmast

val print_rsm_complete_state_info : Format.formatter -> rsm -> unit

val print_rsm_simple_info : Format.formatter -> rsm -> unit

val print_path : Format.formatter -> state list -> unit

(** Returns the string corresponding to the dot representation of the rsm  *)
val string_rsm : ?cex:Rsmast.RState.Set.t -> rsm -> string
