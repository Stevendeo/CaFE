open Rsmast 
open Formula_datatype

type counter_example = (Ext_state.t list * Atoms.raw_atom) list * (((Ext_state.t list) * Id_Formula.Set.t) list)


exception Path_found of counter_example

val search_paths : 
  Rsmast.rsm ->
  (Rsmast.Ext_state.t list * Atoms.raw_atom) list Rsmast.RState.Hashtbl.t Rsmast.RState.Hashtbl.t ->
  (Rsmast.Ext_state.t list * Formula_datatype.Id_Formula.Set.t) list
    Rsmast.RState.Hashtbl.t Rsmast.RState.Hashtbl.t -> 
  counter_example list
  
