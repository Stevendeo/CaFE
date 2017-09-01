(* open Caretast *)
(** AST of a Recursive RState Machine. *)
open Formula_datatype
open Atoms

(** 1. Definition of main types *)

type tag = 
    |Inf (** A state holding this tag means it belongs to an infinite path *)
    |Fin (** A state holding this tag means it belongs to an finite path *)

type info = 
  |Tag of tag
  |TagR (** Considered as tag fin *)

  (** The two last fields are used for generalized buchi condition in 
      the case this RSM is a RGBA. The accepting condition is :
      
      There is a path going infinitely often through the states of each 
      following sets :
      - RStates tagged as Inf 
      - For each Global Until and Abstract Until formula in the closure,
      there is a set of states in which the said formula is true.
  *)

(** 2. Definition of the types in temporary modules to remove incomprehensible warnings. *)
module RState_Make_Input : sig end
module Box_Make_Input : sig end

(** 3. Module types of RSM structure *)

module rec Type_RState : 
  (sig
    type t = {  
      s_id : int ;                    (** Identification of the 
						  node  *)
      mutable s_name : string ;               (** RState name  *)
      mutable deleted : bool ; (** True iff the node is deleted *)
      mutable s_accept : Id_Formula.Set.t ;   (** Set of buchi conditions 
						  the state 
						  satisfies. *)
      mutable call : (Type_Box.t * RState.Set.t) option ;   (** Some box is the state 
						     calls 
						     a module via a box 
						     (call state) 
						     else None *)
      mutable return : (Type_Box.t * RState.Set.t) option ; 
      (** Some box if the state returns from a box (return state), else None *)
      
      (** Use the plug functions in Rsm.mli to change the two previous 
      fields. *)
      
      mutable s_stmt : Cil_types.stmt ; (** Statement corresponding to the 
					    state *)
      mutable s_atom : atom ; (** Atom hold by the state  *)
      mutable s_info : info ; (** Information hold by the state  *)
      mutable s_mod : Type_Rsm_module.t ;(** Module in which the state is. *)
      mutable s_succs : RState.Set.t ; 
      (** RStates accessible from this state *)

      mutable s_preds : RState.Set.t ; 
      (** Predecessors of this state *)
      
      mutable summary_succs : 
	(((Ext_state.t list) * Id_Formula.Set.t) list) RState.Map.t  ; 
      mutable summary_preds : RState.Set.t ;
    }
   end)

and Ext_state:
  (
    sig 
      type t = 
	State of Type_RState.t 
      | Summary of (t list * Id_Formula.Set.t) list 
	  
      val equal : t -> t -> bool
      val to_state : t -> Type_RState.t
    end)

and Type_Box: ( sig 
  type t = 
    {
      
      b_id : int ;              (** Box's ID *)
      mutable b_name : string ;         (** Name of the box  *)
      mutable r_mod_repres : Type_Rsm_module.t ; (** Module represented by the box  *)
      mutable r_mod_belong : Type_Rsm_module.t ; (** Module the box belong to *)
      mutable box_atom : atom ;         (** Atom hold by the box *)
      mutable box_tag : tag ;           (** Tag hold by the box  *)
      
      (** The "plug" part. These lists refers to the transition 
	  between a call / an exit to an entry / a return. *)
      mutable b_entries : RState.Set.t RState.Map.t;
      mutable b_exits : RState.Set.t RState.Map.t 
	
    }
end )

and Type_Rsm_module: 
  sig 
    type t = 
	{
	  mutable mid : int ;             (** Numerical ID of the module *)
	  mod_name : string ;             (** Module name. Invariant : the main
					      module must be called "main" *)
	  is_func : Cil_types.varinfo ;   (** Function represented by the 
					      module *)
	  mutable states : RState.Set.t ;   (** RStates of the module *)
	  mutable entries : RState.Set.t ;  (** RStates at the beginning of a 
				      module *)
	  mutable exits : RState.Set.t ;    (** RStates at the end of a module *)
	  
	  mutable box_repres : Box.Set.t ; (** Boxes that represents this module *)
	  mutable box_belong : Box.Set.t   (** Boxes that belong to this module *)
	}
  end  

(** Definition of temporary structures used inside the previous types. *)

and RState: (Datatype.S_with_collections with type t = Type_RState.t)

and Box: 
  sig 
    include (Datatype.S_with_collections with type t = Type_Box.t)
  end
and Rsm_module : Datatype.S_with_collections with type t = Type_Rsm_module.t
(* module Box: Datatype.S_with_collections with type t = Type_Box.t
module RState : Datatype.S_with_collections with type t = Type_RState.t	   
*) 
type rsm = {

  rsm_id : int ;                    (** Unique Id of the rsm *)
  mutable name : string;            (** Name of the rsm  *)
  mutable rsm_mod : Rsm_module.Set.t; (** Module list of the automaton *)
  mutable start : RState.Set.t ;      (** Initial states of the automaton *)
 
  mutable until_set : Id_Formula.Set.t; (** Set of the Buchi conditions. *)
}

type state = Type_RState.t
type box = Type_Box.t
type r_module = Type_Rsm_module.t
type extended_state = Ext_state.t

module Config : (Datatype.S_with_collections with type t = state * box list)
  
