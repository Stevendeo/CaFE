open Rsmast 
open Formula_datatype

exception Counter_example_failure

(* Deletes states according to a wp calculation *) 
val testAcceptance : rsm -> unit
