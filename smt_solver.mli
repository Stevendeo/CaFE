open Formula_datatype

exception Smt_query_failure

val cvcTest: Id_Formula.Set.t -> bool

type smt_answer = 
| Sat 
| Unsat 
| Unknown

val z3_answer :  ?vars : Cil_types.logic_var list -> Cil_types.predicate ->smt_answer

val pred_mem : Cil_types.logic_var -> Cil_types.predicate -> bool
