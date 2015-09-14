open Cil_types
open Rsmast 
open Formula_datatype

exception Path_found of 
    Ext_state.t list * (((Ext_state.t list) * Id_Formula.Set.t) list)

val registerValuesLoop: (stmt * Db.Value.callstack * Db.Value.state list) -> unit

val printValueResults : unit -> unit

val analyse_paths : 
  Rsmast.rsm ->
  (Rsmast.Ext_state.t list * 'a) list Rsmast.RState.Hashtbl.t
    Rsmast.RState.Hashtbl.t ->
  (Rsmast.Ext_state.t list * Formula_datatype.Id_Formula.Set.t) list
    Rsmast.RState.Hashtbl.t Rsmast.RState.Hashtbl.t -> unit
  
