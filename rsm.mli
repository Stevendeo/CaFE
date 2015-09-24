open Rsmast
open Caretast
open Formula_datatype
open Atoms

exception Inconsistent_atom of atom_kind

(** 1. Module management *)

(** Creates a customized module. Be careful : this function does no 
    verification about the consistency of it's arguments 
    (transition, states...), so be careful when using non-default arguments.
*)

val mkModule : 
  string -> 
  ?st: RState.Set.t -> 
  ?in_st: RState.Set.t -> 
  ?out_st: RState.Set.t ->  
  Cil_types.varinfo -> 
  r_module

(** The second argument is the module represented by the box, the third is the 
    module the box belongs to. The two states in argument represents 
    respectively the entry (call) and the exit (return) of a box. *)
val mkBox : string -> r_module -> r_module -> Atom.t -> tag  -> box

(** Configues the call parameter of the first state in argument *)
val plugEntryBox : box -> state -> state -> unit

(** Configues the return parameter of the second state in argument *)
val plugExitBox : box -> state -> state -> unit

(** Tells if the module in argument represents the main function *)
val isMainMod: r_module -> bool

val getMainMod : rsm -> r_module

(** 3. RState management  *)

(** Creates a state. 
    Warning : this function doesn't add the state to the module, you have to 
    use addRState. Furthermore, you need to precise manually to which accepting
    state set it belongs to. *)
val mkRState : 
  string -> ?acpt:Id_Formula.Set.t -> Cil_types.stmt -> Atom.t -> info -> 
  r_module -> state

val mkCall : 
  string -> ?acpt:Id_Formula.Set.t -> Cil_types.stmt -> box -> state -> r_module
  -> state

val mkReturn :  
  string -> ?acpt:Id_Formula.Set.t -> Cil_types.stmt -> Atom.t -> box -> state -> r_module 
  -> state

(** Adds a state to the module in argument. The booleans entry & exits are here 
    to specify if the state is at the beginning or the end of the automaton. 
    They are set by defalt to false. *)

(** Returns [true] iff the state is an entry state *)
val isEntry : state -> bool

(** Returns [true] iff the state is an exit state *)
val isExit : state -> bool

val isCall : state -> bool

val isRet : state -> bool

(** Returns the varinfo of the called or returned function by the state. *)
val getCalledFunc : state -> Cil_types.varinfo

val isStart : state -> bool

val isDeleted : state -> bool

val deleteRState : state -> unit

val addRState : state -> ?entry : bool -> ?exits : bool -> r_module -> unit

(** Adds a list of states to the r_module in argument. *)
val addRStates : RState.Set.t -> r_module -> unit

(** Adds a state as an entry to the r_module in argument *)
val addEntry : state -> r_module -> unit
 
(** Adds a state as an exit to the r_module in argument *)
val addExit : state -> r_module -> unit

val addEntries : state list -> r_module -> unit

val addExits : state list -> r_module -> unit

(** Tries to get in the box via the first argument if it is a call or to get 
    out of the box if it is an exit. *)
val throughBox : state -> box -> RState.Set.t

(** Returns a copy of the state in argument *)
(*val copyRState : state -> state
*)
(** 4. Transitions management *)

val mkTrans : state -> state -> unit

(** 5. Rsm generation  *)

val mkEmptyRsm : string -> rsm

(* Returns a brand copy of the previous rsm, with new Ids. *)
(* val copyRsm : rsm -> rsm*)

val addMod : r_module -> rsm -> unit

(** Generates Buchi conditions to the automaton. *)
val generateBuchi : identified_formula list -> rsm -> Id_Formula.Set.t

(** Adds Buchi conditions to a state. Be careful to update the Buchi set with
    generateBuchi before calling this function. *)
val addBuchiToRStates : rsm -> unit 

val setStart : state -> rsm -> unit

val simplifyAutomaton : rsm -> unit

(*val degeneralizeAuto : rsm -> rsm

val acceptance_when_ends : rsm -> bool
*)

val exitReachability : rsm -> unit

(*
val unfoldAutomaton : rsm -> unit
*)
(** Checks if the path found is spurious or not (Todo) *)
(*val isNotSpurious : (state list * state list list) -> bool
*)

val testAcceptance :
  Rsmast.rsm ->
  (Rsmast.Ext_state.t list *
     (Rsmast.Ext_state.t list * Formula_datatype.Id_Formula.Set.t)
            list)
    option

val print_memoizers : unit -> unit
