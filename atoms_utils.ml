open Formula_datatype
open Caretast
open Atoms

module Aid = State_builder.SharedCounter(struct let name = "atom_counter" end)

let new_id = Aid.next
(** 1. Atom utilities *)

let empty_raw_atom = Id_Formula.Set.empty

let mkAtom a_k a = 
  {atom_id = new_id (); a_kind = a_k ; atom = a}

(*let copyAtomWithFunc atom func = 
*)
let getAtomKind atom = atom.a_kind

let getPropsFromAtom atom = atom.atom

let atomicProps atom = 
  Id_Formula.Set.filter
    (fun id_form -> 
      match id_form.form with
      | CProp _ | CNot (CProp _) -> true
      | _ -> false
    )
    (getPropsFromAtom atom)

let formInRawAtom form raw_atom = 

  Id_Formula.Set.exists
    (fun id_form -> Caret_Formula.equal id_form.form form)
    raw_atom

let formInAtom form atom =
  
(*  let infoToAKind = function
    | ICall _ -> ACall
    | IRet _ -> ARet
    | IInt -> AInt
  in*)
    (*let atom_kind = getAtomKind atom in*)
    match form with
      
     (* CInfo i -> atom_kind = i 
    | CNot (CInfo i) -> atom_kind <> i*)
    | CTrue -> true
    | CFalse -> false
    | _ -> formInRawAtom form (getPropsFromAtom atom)

let addForm form atom = 
  atom.atom <- (Id_Formula.Set.add form (getPropsFromAtom atom))

(*let minimizeAtom atom = 
  Id_Formula.Set.filter
    (fun id_form -> )
    (getPropsFromAtom atom)
 
*)
let equalsAtom atom1 atom2 = 

  (getAtomKind atom1) = (getAtomKind atom2) 
  && Id_Formula.Set.equal (getPropsFromAtom atom1) (getPropsFromAtom atom2)

let testIs a = 
  match getAtomKind a with
    ICall _ -> 0
  | IRet _ -> 1
  | IInt -> 2

let isACall a = (testIs a) = 0

let isARet a = (testIs a) = 1

let isAInt a = (testIs a) = 2
