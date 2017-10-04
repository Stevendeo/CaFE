open Caretast
open Formula_datatype

type atom_kind = info_prop

type raw_atom = Id_Formula.Set.t

let pretty_raw_atom fmt a = 
  Id_Formula.Set.iter
    (fun form -> 
       Format.fprintf fmt "%a\n" 
	 Id_Formula.pretty form
    ) a

type atom = 
  
  {
    atom_id : int;
    a_kind : atom_kind;
    mutable atom : raw_atom;
  }

module Atom:Datatype.S_with_collections with type t = atom = 
  Datatype.Make_with_collections
    (
      struct 
	include Datatype.Undefined
	type t = atom
	let name = "Atom"
	let reprs = [{atom_id = -1; a_kind = IInt;atom = Id_Formula.Set.empty}]
	let equal (a:t) (b:t) = a.atom_id = b.atom_id
	let compare (a:t) (b:t) = Pervasives.compare a.atom_id b.atom_id
	let hash (a:t) = a.atom_id
	let varname (a:t) = 
	  let stringAKind = function
	    | ICall (Some s) -> "Call_" ^ s ^ " - "
	    | ICall _ -> "Call - "
	    | IRet (Some s) -> "Ret_" ^ s ^" - "
	    | IRet _ -> "Ret - "
	    | IInt -> "Int - "
	  in
	  let string_raw_atom set = 
	    Id_Formula.Set.fold
	      (fun f acc ->
		(Id_Formula.varname f)^ " ;\n " ^ acc
	      )
	      set
	      "\n"   
	      
	  in
	  (stringAKind a.a_kind) ^ (string_raw_atom a.atom)
	
	let pretty fmt atom = 
	  pretty_raw_atom fmt atom.atom
      end
      )
