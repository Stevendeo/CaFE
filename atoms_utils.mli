open Caretast
open Atoms
(** 1. Atom utilities *)

(** Combines the atom_kind and the raw_atom *)

val empty_raw_atom : raw_atom

val mkAtom : atom_kind -> raw_atom -> atom

(*val copyAtomWithFunc : atom -> string -> atom
*)
val getAtomKind : atom -> atom_kind

val getPropsFromAtom : atom -> raw_atom

(** Returns a raw_atom with no temporal formula (only simple predicates) *)
val atomicProps : atom -> raw_atom

(** Checks if a formula is in a raw atom *)
val formInRawAtom : caret_formula -> raw_atom -> bool

(** Checks if a formula is in an atom *)
val formInAtom : caret_formula -> atom -> bool

(** Adds an id_formula in an atom *)
val addForm : identified_formula -> atom -> unit

(** Tests if two atoms are exactly the same *)
val equalsAtom : atom -> atom -> bool

(**  *)
val isACall : atom -> bool

val isARet : atom -> bool

val isAInt : atom -> bool

