open Caretast
open Formula_datatype
open Atoms
(** Correspond to a kind of state. We need it to assciate atoms to states *)

exception Unsatisfiable_formula

(** 1. SMT solver query of Cil predicates *)

exception Smt_query_failure

type smt_answer = 
| Sat 
| Unsat 
| Unknown


val z3_answer :  ?vars : Cil_types.logic_var list -> Cil_types.predicate ->smt_answer

(** 2. CaFE Formula utils  *)
val spurious_stmt_hashtbl : Id_Formula.Set.t Cil_datatype.Stmt.Hashtbl.t

(** Formula utilities *)
val mkIdForm : caret_formula -> identified_formula

val getFormula : identified_formula -> caret_formula

val getFormId : identified_formula -> int

val findFormula : caret_formula -> identified_formula list -> identified_formula

(** Atom utilities & generation*)

(** Checks if the propositions (CProp p) of the atom are consistent 
    with the studied statement of the current studied kf.
    If it can't find out, it assumes as correct.*)
val isConsistent : 
  Cil_types.stmt -> ?after:bool -> Cil_types.kernel_function -> atom -> bool

(** Next requirement for raw atoms *)
val nextReq : op_kind -> identified_formula list -> atom -> atom -> bool

(** Abstract Next Requirements  *)
val absNextReq : identified_formula list -> atom -> atom -> bool

(** General Next Requirements *)
val glNextReq : identified_formula list ->  atom -> atom -> bool

val noSideEffectNextReq : ?var:Cil_types.varinfo -> atom -> atom -> bool
(** Caller formulas *)
val callerFormulas : atom -> Id_Formula.Set.t

(** Replaces the occurences of formulas undefined by CaRet : 
    
    - a And b -> Not (Not a or Not b) 
    - Fatally a -> true Until a
    - Globally a -> a Until falsqe
   
*)
val normalizeFormula : caret_formula -> caret_formula

(** Computes the closure of a formula *)
val closure : caret_formula -> identified_formula list

(** Computes the atom list from the closure in argument. *)
val mkAtoms : 
  identified_formula list -> (atom_kind , Atom.Set.t) Hashtbl.t -> unit

val string_spurious : unit -> string

