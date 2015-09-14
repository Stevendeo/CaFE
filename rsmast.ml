open Formula_datatype
open Atoms

(*open Cil_datatype
*)
type tag = 
  |Inf (** A state holding this tag means it belongs to an infinite path *)
  |Fin (** A state holding this tag means it belongs to an finite path *)

type info = 
  |Tag of tag
  |TagR (** Considered as tag fin *)
(*
module RState_Functor:Datatype.Functor_info = struct let module_name = ".Set" end
*)
(*
module type Minimum_Input = 
  sig 
    
    type t 
    val equal :  t -> t -> bool 
    val hash : t -> int
    val compare : t -> t -> int

  end

module type S_with_simple_collections = 
  sig
    type t
    module Set:(FCSet.S with type elt = t)
    module Map: (FCMap.S with type key = t)
    module Hashtbl:(FCHashtbl.S with type key = t)
      
    val equal :  t -> t -> bool 
    val hash : t -> int
    val compare : t -> t -> int

  end

module Make_with_simple_collections (X:Minimum_Input) = 
  
  struct 
    include X
    module Set = FCSet.Make (X)
    module Map = FCMap.Make (X)
    module Hashtbl = FCHashtbl.Make (X)
  end
*)

(* Sorry, but necessary *)

let empty_structure = Obj.magic 0

module rec Type_RState :(
  sig 
    type t = 
      {  
	mutable s_id : int ;                    (** Identification of the 
						    node  *)
	mutable s_name : string ;               (** RState name  *)
	mutable s_accept : Id_Formula.Set.t ;   (** Set of buchi conditions 
						    the state 
						    satisfies. *)
	mutable call : (Type_Box.t *  RState.Set.t) option ;   (** Some box is the state 
						       calls 
						       a module via a box 
						       (call state) 
						       else None *)
	mutable return : (Type_Box.t * RState.Set.t) option ; 
	(** Some box if the state returns from a box (return state), 
						       else None *)
      (** Use the plug functions in Rsm.mli to change the two previous 
      fields. *)
	
	mutable s_stmt : Cil_types.stmt ; (** Statement corresponding to the 
					      state *)
	mutable s_atom : atom ; (** Atom hold by the state  *)
	mutable s_info : info ; (** Information hold by the state  *)
	mutable s_mod : Type_Rsm_module.t ;(** Module in which the state is. *)
	mutable s_succs : RState.Set.t ; (** RStates accessible from this state
				       *)
	mutable s_preds : RState.Set.t ; (** Predecessors of this state *)
      
	mutable summary_succs : RState.Set.t;
	  (*(((Ext_state.t list) * Id_Formula.Set.t) list) RState.Map.t  ; *)
	mutable summary_preds : RState.Set.t ;
      }

  end)
  = 
struct
  type t =  {  
    mutable s_id : int ;                    (** Identification of the 
						node  *)
    mutable s_name : string ;               (** RState name  *)
    mutable s_accept : Id_Formula.Set.t ;   (** Set of buchi conditions 
						the state 
						satisfies. *)
    mutable call : (Type_Box.t *  RState.Set.t) option ;   (** Some box is the state 
						   calls 
						   a module via a box 
						   (call state) 
						   else None *)
    mutable return : (Type_Box.t * RState.Set.t) option ; 
    (** Some box if the state 
	returns from a box 
	(return state), 
	else None *)

      (** Use the plug functions in Rsm.mli to change the two previous 
	  fields. *)
    
    mutable s_stmt : Cil_types.stmt ; (** Statement corresponding to the 
					    state *)
    mutable s_atom : atom ; (** Atom hold by the state  *)
    mutable s_info : info ; (** Information hold by the state  *)
    mutable s_mod : Type_Rsm_module.t ;(** Module in which the state is. *)
    mutable s_succs : RState.Set.t ; (** RStates accessible from this state
				   *)
    mutable s_preds : RState.Set.t ; (** Predecessors of this state *)
    
    mutable summary_succs : RState.Set.t;
      (*(((Ext_state.t list) * Id_Formula.Set.t) list) RState.Map.t  ; *)
    mutable summary_preds : RState.Set.t ;
  }
 
end

and RState_Make_Input:(Datatype.Make_input with type t = Type_RState.t) = 

  struct 
    include Datatype.Undefined
    include Type_RState

    let name = "RState"
    let equal (x:t) (y:t) = 
      x.s_id = y.s_id
	
    let hash (x:t) = x.s_id
    let compare (x:t) (y:t) = 
      Pervasives.compare 
	x.s_id 
	y.s_id
        
    let varname (x:t) =
      "state_" ^ (string_of_int x.s_id) ^ "_" ^ (x.s_name)
	
    let reprs = 
      [{
      s_id = -1;
      s_name = "";
      s_accept = Id_Formula.Set.empty ;
      call = None;
      return = None;
      s_stmt = Cil.mkEmptyStmt ();
      s_atom = List.hd Atom.reprs;
      s_info = TagR;
      s_mod = List.hd Rsm_module.reprs ;
      
      (* Sorry. *)

      s_succs = empty_structure; 
      s_preds = empty_structure;
      summary_succs = empty_structure;
      summary_preds = empty_structure;
       }
      ]

    let copy = Datatype.identity
    let rehash = Datatype.identity
    let mem_project = Datatype.never_any_project
  end

and RState:(Datatype.S_with_collections with type t = Type_RState.t) = 
  Datatype.Make_with_collections (RState_Make_Input)

and Ext_state : sig 
  type t = 
    State of RState.t
  | Summary of (t list * Id_Formula.Set.t) list
      
      
  val equal : t -> t -> bool
  val to_state : t -> RState.t
end
  = 
  struct 
    type t = 
      State of RState.t
    | Summary of (t list * Id_Formula.Set.t) list
	
		  
    let equal s1 s2 = match s1,s2 with
	State s11, State s22 -> RState.equal s11 s22
      | _,_ -> false

    let to_state = function 
      | State s -> s
      | Summary paths -> 
	match (List.hd (fst (List.hd paths))) with 
	  State s -> s 
	| Summary _ -> assert false
  end

and Type_Box: 
  sig 
    type t = 
      {
	
	mutable b_id : int ;              (** Box's ID *)
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
  end 
  =
  struct 
    type t = 
      {
	
	mutable b_id : int ;              (** Box's ID *)
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
  end 
    
and Box_Make_Input:(Datatype.Make_input with type t = Type_Box.t)  =
struct 
  include Datatype.Undefined
  include Type_Box
  
  let name = "Box"
  let equal (x:t) (y:t) = x.b_id = y.b_id 
  let hash (x:t) = Hashtbl.hash x 
  let compare (x:t) (y:t) = Pervasives.compare x.b_id y.b_id
  let varname (x:t) = "box_" ^ (string_of_int x.b_id) ^ "_" ^ (x.b_name) 
  let reprs = 
    [
    {
      b_id = -1;
      b_name = "";
      r_mod_repres = List.hd Rsm_module.reprs;
      r_mod_belong = List.hd Rsm_module.reprs;
      box_atom = List.hd Atom.reprs;
      box_tag = Fin;
      b_entries = empty_structure;
      b_exits = empty_structure;
    }
    ]
  let copy = Datatype.identity
  let rehash = Datatype.identity
  let mem_project = Datatype.never_any_project

end
  
and Box : (Datatype.S_with_collections with type t = Type_Box.t)
  =
  Datatype.Make_with_collections (Box_Make_Input)

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
   = 
  struct
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

and Rsm_module:Datatype.S_with_collections with type t = Type_Rsm_module.t = 
  Datatype.Make_with_collections
    (struct
      include Datatype.Undefined
      include Type_Rsm_module
	  
      let name = "Rsm_module"
          
      let equal (x:t) (y:t) = x.mid = y.mid 
      let compare (x:t) (y:t) = Pervasives.compare x.mid y.mid
      let hash (x:t) = x.mid
      let copy = Datatype.identity
      let rehash = Datatype.identity
      let mem_project = Datatype.never_any_project
	
      let varname (m:t) = "module_" ^ m.mod_name

      let reprs = 
        [{
	  mod_name = "";
	  is_func = (
	    Cil.makeGlobalVar 
	      "__tmp__" 
	      (Cil_types.TVoid 
		 []));
	  states = empty_structure;
	  entries = empty_structure;
	  exits = empty_structure;
	  mid = -1;     
	  box_repres = empty_structure;
	  box_belong = empty_structure;
      }]
     end)

type rsm = {

  rsm_id : int ;                    (** Unique Id of the rsm *)
  mutable name : string;            (** Name of the rsm  *)
  mutable rsm_mod : Rsm_module.Set.t; (** Module list of the automaton *)
  mutable start : RState.Set.t ;      (** Initial state of the automaton *)

  (** The two last fields are used for generalized buchi condition in 
      the case this RSM is a RGBA. The accepting condition is :
      
      There is a path going infinitely often through the states of each 
      following sets :
      - RStates tagged as Inf 
      - For each Global Until and Abstract Until formula in the closure,
      there is a set of states in which the said formula is true.
  *)
  (*mutable inf_states : state list;*)
 
  mutable until_set : Id_Formula.Set.t; (** Set of the Buchi conditions. *)


}

type state = Type_RState.t
type box = Type_Box.t
type r_module = Type_Rsm_module.t
type extended_state = Ext_state.t

module Config: (Datatype.S_with_collections with type t = state * (box list))
  = 
  Datatype.Make_with_collections(
    struct
      include Datatype.Undefined
      type t = RState.t * Box.t list
      
      let name = "Config"
      let varname ((x,_):t) = RState.varname x (* todo : make it better *)
      let hash (x:t) = Hashtbl.hash x
      let reprs = [(List.hd RState.reprs , Box.reprs)]
	
      let equal ((s1,b1):t) ((s2,b2):t) = 
	RState.equal s1 s2 && 
	  (List.for_all2
	     Box.equal
	     b1
	     b2
	  )
	  
      let compare ((s1,b1):t) ((s2,b2):t) = 
	
        if RState.equal s1 s2
	then
	  
	  let rec comp_b_lists b1 b2 =
	    match b1,b2 with
	      hd1 :: tl1 , hd2 :: tl2 ->
		if Box.equal hd1 hd2
		then comp_b_lists tl1 tl2
		else Box.compare hd1 hd2
	    | [] , [] -> 0
	    | [] , _ -> -1
	    | _ , [] -> 1
	      
	  in
	  
	  comp_b_lists b1 b2
	else
	  RState.compare s1 s2
	    
      let copy = Datatype.identity
      let rehash = Datatype.identity
      let mem_project = Datatype.never_any_project
	  
    end
  )
