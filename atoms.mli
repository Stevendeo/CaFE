(* open Caretast *)
open Formula_datatype

type atom_kind = Caretast.info_prop 
(* because atoms must have the information *)

type raw_atom = Id_Formula.Set.t

type atom = 
  
  {
    atom_id : int;
    a_kind : atom_kind;
    mutable atom : raw_atom;
    
  }

module Atom:Datatype.S_with_collections with type t = atom
