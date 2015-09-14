open Rsmast
open Cil_types
open Cil_datatype
open Dataflow2

(* 1. Backward dataflow analysis definition *)
type if_tag = Then | Else 
(* stmt -> if_stmt * if_tag *)
(*
type wp_stmt = 
| Ins of logic_var * term (* x := e *)
| Assert of predicate
| Assume of predicate
| Div of term * reg_wp_stmt list * reg_wp_stmt list
| Other

and reg_wp_stmt = 
  {
    st : stmt
    wp_st : wp_stmt

  }
*)
let if_stmt_hashtbl = Stmt.Hashtbl.create 12
  
let update_table if_stmt b1 b2 =
  List.iter
    (fun s -> Stmt.Hashtbl.add if_stmt_hashtbl s (if_stmt * Then))
    b1;
  List.iter
    (fun s -> Stmt.Hashtbl.add if_stmt_hashtbl s (if_stmt * Else))
    b2
    
    
    
(*
  let rec weakest_precond ?(l = false) wp_stmt_list pred = 
  List.fold_right
  (fun pred rwp_stmt -> 
  match rwp_stmt.wp_st with
  Ins (lvar,term) -> 
  if l 
  then 
  let equality = Prel (Req, Logic_vconst.tvar lvar, term)
  in
  Pand
  (unamed pred)
  (unamed equality)
  else
  
  let visitor = change_var_to_term lvar term
  in
  
  Visitor.visitFramacPredicate
  (visitor :> Cil.cilVisitor) 
  pred
  
  | Assert q -> Pand ((unamed pred),(unamed q))
  | Assume q -> 
  if l 
  then Pimplies ((unamed pred),(unamed q))
  else Pand ((unamed pred),(unamed q))
  
  | Div (s1,s2) -> 
  let wlp_false = 
  Pand
  (unamed (weakest_precond true s1 Pfalse), 
  unamed (weakest_precond true s2 Pfalse))
  
  in
  if l 
  then 
  Pand
  ((unamed pred),(unamed wlp_false))
  else
  
  let wp_true = 
  
  Pand
  (unamed (weakest_precond s1 Ptrue),
  unamed (weakest_precond s2 Ptrue))
  
  in
  let wp_const = 
  Pand 
  (unamed wlp_false)
  (unamed wp_true)
  in
  
  Pand
  (unamed pred)
  (unamed wp_const)
  
  | Other -> pred
  )
  pred
  wp_stmt_list*)
(* k_f -> predicate *)
    
let wp_results_table = Kernel_function.Hashtbl.create 101
  
let if_stack = Stmt.Stack.create 3
  
module Efac : BackwardsTransfer with type t = predicate = 
struct
  
  module CafeStartData:StmtStartData with type data = predicate 
    =
    StartData(struct type t = predicate let size = 103)
      
  let name = "CaFE_backward_analysis"
  let debug = true
  type t = CafeStartData.data
    
  let var_map = Varinfo.Hashtbl.create 13 (* 13 = number of vars *)
    
  let get_lvar var = 
    try Varinfo.Hashtbl.find var_map var 
    with 
      Not_found -> 
	let res = cvar_to_lvar var 
	in 
	let () = var_map := Varinfo.Hashtbl.add var_map var res
	in
	res
	  
  let get_new_lvar var = 
    if Varinfo.Hashtbl.mem var_map var 
    then 
      let res = make_temp_logic_var (Ctype v.vtype)
      in
      let () = 
	res.lv_name := var.vname ^ "_"  ^ (string_of_int res.lv_id);
	lv_origin := Some var;
	Varinfo.Hashtbl.replace var_map var res
      in
      res
    else get_lvar var
      
      
  class change_var_to_term lvar term = 
  object(self)
    inherit Visitor.frama_c_inplace
      
    method! vterm term = 
      match term.term_node with
	TLval ((TVar logic_var), _) -> 
	  
	  if Logic_var.equal lvar logic_var
	  then
	    ChangeTo term
	  else DoChildren
      | _ -> DoChildren
	
  end
    
  class update_lvars () = 
  object(self)
    inherit Visitor.frama_c_inplace
      
    method! vlogic_var_use lvar = 
      match lvar.lv_origin with
	None -> Caret_option.fatal "Bad initialisation of variable"
      | Some v -> ChangeTo (Varinfo.Hashtbl.find var_map v)
	
  end	  
    
  let update_pred_about_var vinfo exp pred = 
    
    let logic_var = get_lvar vinfo
    in
    
    let new_term = (Logic_utils.expr_to_term (cast:true) exp)
    in
    
    let visitor = new change_var_to_term logic_var new_term
    in
    
    Visitor.visitFramacPredicate (visitor :> Cil.cilVisitor) pred
      
  let correct_term_from_exp exp = 
    
    let exp_termed = Logic_utils.expr_to_term exp 
    in
    
    let visitor_updating_exp = 
      new update_lvars ()
    in
    Visitor.visitFramacTerm 
      (visitor_updating_exp :> Cil.cilVisitor) 
      exp_termed	  
      
  let pretty = Printer_api.pp_predicate
    
  let funcExitData = Pfalse
    
  let combineStmtStartData _ = assert false
    
  let combineSuccessors succ1 succ2 = 
    Por ((Logic_const.unamed succ1),(Logic_const.unamed succ2))
      
  let rec treat_if exp b1 b2 = (* -> predicate *)
    
    let then_stmts = b1.bstmts in 
    let else_stmts = b2.bstmts in
    let old_binds = 
      Varinfo.Set.fold
	(fun varinfo acc -> 
	  Varinfo.Map.add varinfo (get_lvar varinfo) acc)
	Varinfo.Map.empty
	(Varinfo.Set.union 
	   (Varinfo.Set.of_list b1.blocals)
	   (Varinfo.Set.of_list b2.blocals)) (* todo : delete the double 
						more efficiently *)
	
      (* As we modify the hashtbl in the then part, we need to 
	 remeber the old bindings to use them in the else part. *)
	
    in
    let treat_block block = 
      
	(* We will treat a block B of an if statement. We need to compute 
	   two predicates : 
	   wp(B,Ptrue) and wlp(B,Pfalse). *)
      
      List.fold_right
	(fun (wp,wlp) stmt -> 
	  match stmt.skind with
	    If (e,b1,b2) -> 
	      let if_pred = unamed (treat_if e b1 b2)
	      in
	      (Pand 
		 ((unamed wp),
		  if_pred)
	      ),
	      (Pand 
		 ((unamed wlp),
		  if_pred)
	      )
	  | Instr i ->
	    begin
	      match i with 
		Set (Var v, exp, _) -> 
		  
		  let correc_term = correct_term_from_exp exp 
		  in
		  
		  let new_reprs_for_v = 
		    get_new_lvar v
		  in
		  let lval_term = 
		    Logic_utils.expr_to_term (evar new_reprs_for_v)
		  in
		  
		  let new_pred = 
		    unamed 
		      (Prel (Req, lval_term, correct_term))
		  in
		  ((Pimplies
		      new_pred
		      (unamed wp)),
		   
		   (Pimplies
		      new_pred
		      (unamed wlp)))
		    
	      | _ -> pred_acc (* todo : treat the rest *)
	    end
	      
	  | Return _ 
	  | Goto _
	  | Break _
	  | Continue _
	  | Loop
	  | Block
	  | UnspecifiedSequence _
	  | Throw _
	  | TryCatch _
	  | TryFinally _
	  | TryExcept _ -> (wp,wlp)
	    
	  | Switch _ -> assert false	
	)
	(Ptrue,Pfalse)
	block.bstmts
    in
    let then_wp,then_wlp = treat_block b1
    in
    let then_const_form =
      Pand
	((unamed then_wp),
	 (unamed then_wlp))
    in
    
    let () = 
      Varinfo.Map.iter
	(fun vi lv -> 
	  Varinfo.Hashtbl.replace var_map vi lv)
	old_binds
    in
    let else_wp,else_wlp = treat_block b2
    in
    let else_const_form =
      Pand
	((unamed then_wp),
	 (unamed then_wlp))
    in
      (* We now unify the variable out from the then part and the else part *)
    let map_of_varinfos =
      Varinfo.Set.fold
	(fun v _ acc -> 
	  let old_reprs_for_v = get_lvar v
	  in
	  
	  let new_reprs_for_v = 
	    get_new_lvar v
	  in
	  
	  Prel 
	    (Req, 
	     (Logic_const.tvar old_reprs_for_v), 
	     (Logic_const.tvar new_reprs_for_v))
	    
	)
	old_binds
	[]
    in
    
    let correct_term = correct_term_from_exp exp
    in 
    
    List.fold_left
      (fun acc mapping -> 
	Pand 
	  (unamed acc)
	  (unamed mapping)
      )
      map_of_varinfos
      (Pif (correct_term, then_const_form, else_const_form))
      
  let doStmt s = 
    
    if Stmt.Hashtbl.mem if_stmt_hashtbl s
    then 
      Done 
	(try CafeStartData.find s
	 with Not_found -> funcExitData)
    else
      match s.skind with
	Instr _
      | Return
      | Goto _
      | Break _
      | Continue _
      | Loop
      | Block
      | UnspecifiedSequence 
      | Throw _
      | TryCatch _
      | TryFinally _
      | TryExcept _ ->  
	Default
	  
      | If (exp,b1,b2,_) -> 
	Done (treat_if exp b1 b2)
	  
      | Switch _ -> assert false
	
  let doInstr _ i pred =
    match i with
      Call _ 
    | Asm _ 
    | Skip _ -> Default
      
    | Code_annot _ -> Default 
      (* todo : 
	 - if proved, get results 
	 - treat assertions *)
      
    | Set ((lhost,_),exp) ->
      match lhost with 
	Var v -> 
	  Done (update_pred_about_var v exp pred)
      | Mem _ -> Default (* todo : treat tab *)
	
  let filterStmt _ _ = true
    
end
  
module Cafe_Backward = Backwards (Efac)
