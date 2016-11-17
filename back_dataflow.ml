open Cil
open Cil_types
open Cil_datatype
open Dataflow2
open Logic_const
(*
module Pid = State_builder.SharedCounter
  (struct let name = "predicate_counter" end)

let new_pid = Pid.next
*)

let dkey_stmt = Mat_option.register_category "back_dataflow:doStmt"
let dkey_if = Mat_option.register_category "back_dataflow:if_cond"
type if_tag = Then | Else 

type if_stmt = stmt * if_tag

(** 1. Predicate utilities *)

let cvc_test p = 
  
  let str_pred = 
    Mat_printer.predicate_to_cvc p
  in
  
  Mat_option.debug "%s" str_pred;
  (*let par_op = Str.regexp "(" in 
  let par_cl = Str.regexp ")" in 

  let str_pred = 
    Str.global_replace 
      par_op 
      "\\("
      cvc_str
  in
  
  let str_pred = 
    Str.global_replace par_cl 
       "\\)" 
       str_pred 
  in*)
  let str_pred = 
    ("prop: BOOLEAN =" ^  str_pred ^ "; CHECKSAT prop;")
  in
  let echo_cmd = "echo \"" ^ str_pred  ^ "\" > __smt_cafe_tmp.cvc" in 
  let cvc_cmd = "cvc3 __smt_cafe_tmp.cvc > __smt_res.txt" in 

  if Sys.command echo_cmd <> 0
  then  Mat_option.abort "failed to run cvc3 : echo failed"
  else 
    let () = Mat_option.debug "echo ok" in
    
    if Sys.command cvc_cmd <> 0
    then Mat_option.abort "failed to run cvc3"
    else 
      let () = Mat_option.debug "cvc3 ok" in
      
      let file = open_in "__smt_res.txt" in
      let result = input_line file in 
      let () = close_in file
      in
      match result with
	"Satisfiable." -> true
      | "Unsatisfiable." -> false
      | _ -> Mat_option.abort "cvc crashed : %s" result

let predicate_to_dreal pred = 

  let rel_str = 
    function
    | Rlt -> "<"
    | Rgt -> ">"
    | Rle -> "<="
    | Rge -> ">="
    | Req -> "="
    | Rneq -> assert false
  in
  let treat_term term = 
    String.trim
      (Format.fprintf 
	 Format.str_formatter 
	 "@[%a@]" 
	 Printer.pp_term 
	 term;
       Format.flush_str_formatter ()
      )
  in
  
  let rec treat_pred p = 
    match p.pred_content with
    | Pfalse -> "false"
    | Ptrue -> "true"
    | Prel (rel,t1, t2) -> 
      (rel_str rel) ^ " (" ^ (treat_term t1)  ^ ") (" ^(treat_term t2) ^ ")"
    | Pand (p1, p2) -> 
      "and (" ^ (treat_pred p1)  ^ ") (" ^(treat_pred p2) ^ ")"
    | Por (p1, p2) -> 
      "or (" ^ (treat_pred p1)  ^ ") (" ^(treat_pred p2) ^ ")"
    | Pimplies (p1, p2) -> 
      "=> (" ^ (treat_pred p1)  ^ ") (" ^(treat_pred p2) ^ ")"
    | Piff (p1, p2)-> 
      "iff (" ^ (treat_pred p1)  ^ ") (" ^(treat_pred p2) ^ ")"
    | Pxor (p1, p2) -> 
      "xor (" ^ (treat_pred p1)  ^ ") (" ^(treat_pred p2) ^ ")"
    | Pnot p -> "not (" ^ (treat_pred p) ^ ")"
    | _ -> 
      Mat_option.fatal "What do we have here... @[%a@]" 
	Printer.pp_predicate pred
	
  in
  "(assert (" ^ (treat_pred pred) ^ ")"

(** 2. Dataflow *)

let (if_stmt_hashtbl : if_stmt Stmt.Hashtbl.t) = Stmt.Hashtbl.create 12
  

let update_table if_stmt b1 b2 =
  List.iter
    (fun s -> Stmt.Hashtbl.add if_stmt_hashtbl s (if_stmt,Then))
    b1;
  List.iter
    (fun s -> Stmt.Hashtbl.add if_stmt_hashtbl s (if_stmt,Else))
    b2
    
let (loop_hashtbl : stmt Stmt.Hashtbl.t) = Stmt.Hashtbl.create 12

let update_loop_table loop_stmt b =
  List.iter
    (fun s -> Stmt.Hashtbl.add loop_hashtbl s loop_stmt)
    b

let lvar_created = ref []
 
let (wp_results_table : predicate Kernel_function.Hashtbl.t)
    = Kernel_function.Hashtbl.create 101
  
module CafeStartData:(
  StmtStartData with type data = predicate * (logic_var list) )
  =
  StartData (struct type t = predicate * (logic_var list) let size = 103 end)
    
    
module type P = sig val pred : predicate  * (logic_var list) end
    
module Efac (Pred : P): 
  BackwardsTransfer with type t = predicate * (logic_var list) = 
struct

  module StmtStartData = CafeStartData
  let name = "CaFE_backward_analysis"
  let debug = true
  type t = CafeStartData.data
    
  let treated_stmt = ref Stmt.Set.empty

  (* 1. Variable manipulation through the dataflow *)

  let var_map = ref Varinfo.Map.empty
    
  let map_add v lv = var_map := Varinfo.Map.add v lv !var_map

  let var_map_init () = 
    let vis = 
      
     object
       inherit Visitor.frama_c_inplace
	 
       method! vlogic_var_use var = 
	 match var.lv_origin with
	   Some v -> 
	     map_add v var; SkipChildren
	 | None -> assert false
	   
     end
    in      
    Cil.visitCilPredicate (vis :> Cil.cilVisitor) (fst Pred.pred)
      
  let () = ignore (var_map_init ())
  
  let get_lvar var = 
    try Varinfo.Map.find var !var_map
    with 
      Not_found -> 
	let () = 
	  Mat_option.debug 
	    "@[%a@] never seen : registering"
	    Printer.pp_varinfo
	    var
	in
	let res = cvar_to_lvar var 
	in 
	
	let () = 
	  map_add var res; 
	  lvar_created:= res ::!lvar_created
	in
	res
	  
  let get_new_lvar var = 
    let () =  
      Mat_option.debug 
	"New variable for %a"
	Printer.pp_varinfo var in
    if Varinfo.Map.mem var !var_map 
    then 
      let res = make_temp_logic_var (Ctype var.vtype)
      in
      

      let () = 
	res.lv_name <- var.vname ^ "_"  ^ (string_of_int res.lv_id);
	res.lv_origin <- Some var;
        map_add var res;
	lvar_created := res :: !lvar_created
      in
      let () = 
	Mat_option.debug 
	  "New representant for @[%a@] : @[%a@]"
	  Printer.pp_varinfo 
	  var
	  Printer.pp_logic_var 
	  res
      in
      res
    else get_lvar var
      
      
  let change_var_to_term lvar term = 
    
  object
    inherit Visitor.frama_c_inplace
      
    method! vterm t = 
      match t.term_node with
	TLval ((TVar logic_var), _) -> 
	    
	  if Logic_var.equal lvar logic_var
	  then
	    
	    ChangeTo term
	  else DoChildren
      | _ -> DoChildren
	
  end
    
  let update_lvars = 
  object
    inherit Visitor.frama_c_inplace
      
    method! vlogic_var_use lvar = 
      match lvar.lv_origin with
	None -> Mat_option.fatal "Bad initialisation of variable"
      | Some v -> 
	ChangeTo (get_lvar v)
	
  end	  
   
exception Not_a_simple_loop

let loop_to_the_n b loop_cond = 
  let var_index_map,mat_list = 
    try 
      Slap_utilities.analyse_block b
    with Slap_utilities.Non_linear_loop -> Varinfo.Map.empty,[]
  in
  let () = 
      (* Adding forgotten variables to the var_map *)
    Varinfo.Map.iter
      (fun v _ -> ignore (get_lvar v))
      var_index_map
  in
  match mat_list with
    [] -> Ptrue
      
  | _ :: _ :: _ -> 
    Mat_option.debug "We don't treat conditions in loops yet"; 
    Ptrue

  | s_mat :: _ -> 
    
      let p,t,pm = 
	  try
	    Slap_utilities.trigon_matrix
	      (Slap_utilities.copy_mat s_mat)
	  with
	    Slap_utilities.Complex_eigen_values -> 
	      Mat_option.debug
		"Complex eigen values."; raise Not_a_simple_loop
      in
      let () = 
	Mat_option.debug ~level:2 ~dkey:dkey_stmt
	  "P = @[%a@]\nT = @[%a@]\nP-1 = @[%a@] "
	  Lacaml_D.pp_mat p
	  Lacaml_D.pp_mat t
	  Lacaml_D.pp_mat pm
	  
      in
      let open Matrix in
      
      let t_term = t |> float_lacaml_to_float |> to_the_n in
      
      Mat_option.debug ~level:2
	"T to the n gives\n @[%a@]"
	Term_M.pp_mat (t_term)
      ;
      let p_term = p |> float_lacaml_to_float |> float_to_term
      in
      let pinv_term = pm |> float_lacaml_to_float |> float_to_term
      in
      let mat_n = 
	Term_M.mult 
	  p_term 
	  (Term_M.mult t_term pinv_term)
      in
      
      let old_var_map = !var_map in
      
      let term_one_step_mat = s_mat |> float_lacaml_to_float |> float_to_term
      in
      
      let term_one_step_map =  
	Matrix.mat_to_terms 
	  !var_map 
	  var_index_map
	  term_one_step_mat
      in
      
      let () = (* updates all variables *)
	Varinfo.Map.iter
	  (fun vinf _ -> 
	    ignore (get_new_lvar vinf)
	  )
	  term_one_step_map
      in
      
      
      let end_loop_pred = 
	  (* This predicate specifies whether one iteration of the loop 
	     ends up in the final state by starting in a state satisfying the 
	     loop_condition *)
	Varinfo.Map.fold
	  (fun vinf term acc ->
	    let old_var = Varinfo.Map.find vinf old_var_map
	      in
	    
	    let correct_term = 
	      Cil.visitCilTerm (update_lvars :> Cil.cilVisitor) term
	    in
	    let lval_term = Logic_const.tvar old_var
	    in
	    let eq_pred = 
	      Prel 
		(Req,
		 lval_term,
		 correct_term)
	    in
	    if acc = Ptrue then eq_pred 
	    else
	      Pand
		((unamed acc),
		 (unamed eq_pred)) 
	  )
	  term_one_step_map
	  (Pnot loop_cond)
	  
      in
      
      let term_mat_n_map = 
	  (* terms corresponding to matrix lines, 
	     in the var_map iteration order *)
	Matrix.mat_to_terms !var_map var_index_map mat_n
      in
      
      let old_var_map = !var_map
      in
      let new_loop_cond = 
	Cil.visitCilPredicate 
	  (update_lvars :> Cil.cilVisitor)
	  loop_cond
      in
      let () = (* updates all variables of var_map *)
	Varinfo.Map.iter
	  (fun vinf _ -> 
	    ignore (get_new_lvar vinf)
	  )
	  term_mat_n_map
      in
      
      let other_iterations = 
	  (* This predicate specifies whether we can satisfy the previous 
	     predicate by taking n loop and still satisfy the loop_condition *)
	
	Varinfo.Map.fold
	  (fun vinf term acc ->
	    let old_var = Varinfo.Map.find vinf old_var_map
	    in
	    
	    let correct_term = 
	      Cil.visitCilTerm (update_lvars :> Cil.cilVisitor) term
	    in
	    let lval_term = Logic_const.tvar old_var
	    in
	    let eq_pred = 
	      Prel 
		(Req,
		 lval_term,
		 correct_term)
	    in
	    if acc = Ptrue then eq_pred 
	      else
	      Pand
		((unamed acc),
		 (unamed eq_pred)) 
	  )
	  term_mat_n_map
	  new_loop_cond.pred_content
      in
      
      Pand ((unamed other_iterations),(unamed end_loop_pred))
  
  let correct_term_from_exp exp = 
    
    let () = 
      Mat_option.debug "Exp : @[%a@]" Printer.pp_exp exp
    in
    let exp_termed = Logic_utils.expr_to_term ~cast:false exp 
    in
    
    let term = 
      Cil.visitCilTerm 
	(update_lvars :> Cil.cilVisitor) 
	exp_termed	  
    in
    
    let term = 
      match term.term_node with  
	TCastE (typ,t) ->
	  Logic_const.term t.term_node (Logic_utils.typ_to_logic_type typ)
      | _ -> term
    in
    let () = 
      Mat_option.debug "Term : @[%a@]" Printer.pp_term term
    in
    term
    
  let if_conds_as_pred (s : stmt list) : predicate = 
    let __if_conds_as_preds stmt = 
      
	
	let () = Mat_option.debug ~dkey:dkey_if ~level:3 
	  "If statement : @[%a@]"
	  Printer.pp_stmt stmt
	in
	let term = 
	  match stmt.skind with
	    If (e,_,_,_) -> correct_term_from_exp e 

    (*else 
      TBinop (LAnd,t,acc)
      (** TODO : HERE WE NEED TO COMPLETE THE MULTIPLE CONDITION  **)*)
      | _ -> assert false
	in
	match term.term_node with
	  TBinOp(Eq,t1,t2) -> 
	    Prel (Req,t1,t2)
	| TBinOp(Ne,t1,t2)  -> 
	    Prel (Rneq,t1,t2)
	| TBinOp(Lt,t1,t2)  -> 
	    Prel (Rlt,t1,t2)
	| TBinOp(Gt,t1,t2)  -> 
	    Prel (Rgt,t1,t2)
	| TBinOp(Ge,t1,t2)  -> 
	    Prel (Rge,t1,t2)

	| _ -> 
	
	Prel
	  (Rneq, term, (* 0 *)
	   Logic_const.term 
	     (TConst (Integer (Integer.zero,None))) 
	     Linteger)
	
    in
    unamed 
      (List.fold_left  
      (fun acc s -> 
	let pred = __if_conds_as_preds s in 
	if acc = Ptrue then pred else 
	  Pand(unamed pred, unamed acc ) 
      ) 
      Ptrue 
      s
      ) 

  let update_pred_about_var vinfo exp pred = 
    
        
    let new_term = correct_term_from_exp exp
    in

    if not (Varinfo.Map.mem vinfo !var_map)
    then
      let () = Mat_option.debug "%s not registered" vinfo.vname
      in
      
      let new_var = get_new_lvar vinfo
      in
      unamed (Pand
	((unamed pred),
	(unamed (Prel (Req, (tvar new_var), new_term)))))
    else
      

      let logic_var = get_lvar vinfo
      in
      let () = 
	Mat_option.debug "@[%a@] replaced by @[%a@]"
	  Printer.pp_logic_var 
	  logic_var
	  Printer.pp_term
	  new_term
      in
      
      let visitor = change_var_to_term logic_var new_term
      in
      (Cil.visitCilPredicate (visitor :> Cil.cilVisitor) (unamed pred))

  let uniformize old_vars = 
  (* creates a predicate binding every variable of old_vars to the actual
     var registered. *)
    List.fold_left
      (fun acc l_var ->
	let () = 
	  Mat_option.debug
	    ~level:2
	    ~dkey:dkey_stmt
	    "Old lvar : @[%a@]"
	    Printer.pp_logic_var
	    l_var
	in
	match l_var.lv_origin with
	  None -> acc 
	| Some v_orig ->  
	  
	  try
	    let new_var = Varinfo.Map.find v_orig !var_map
	    in
	    if Logic_var.equal new_var l_var
	    then acc
	    else
	      Pand
		(unamed acc,
		 unamed 
		   (Prel 
		      (Req, 
		       Logic_const.tvar new_var, 
		       Logic_const.tvar l_var)))
		   
	  with
	    Not_found (* find *) -> acc
      )
      Ptrue 
      old_vars
      

  (* 2. Dataflow functions *)

  let pretty fmt (p,_) = Printer.pp_predicate fmt p
    
  let funcExitData = Pred.pred
    
  let combineStmtStartData s ~old newd =
    let () = 
      Mat_option.debug ~level:2
	
	"Statement %a :\n old = @[%a@]\npred = @[%a@] "
	Printer.pp_stmt
	s
	Printer.pp_predicate
	(fst old)
	Printer.pp_predicate
	(fst newd)
    in
    if Stmt.Set.mem s !treated_stmt 
    then 
      let () = 
	Mat_option.debug ~level:2 "Statement already treated" in
	None
    else 
      let () = 
	Mat_option.debug ~level:2 "Statement never treated" in
      let () = treated_stmt := Stmt.Set.add s !treated_stmt
      in
      
      match s.skind with 
	Loop _ ->
	  let () = 
	    Mat_option.debug ~level:4 "This is a loop" in
	  let p_old,_ = old
	  in 
	  let p_new,v_new = newd
	  in
	  
	  let new_pred = 
	    unamed (Pand(p_new, p_old))
	  in
	  let () =  
	    StmtStartData.add s (new_pred,v_new) 
	  in Some (new_pred,v_new) 
      | _ -> 
      let () = 
	Mat_option.debug ~level:2 "This is not a loop, we keep the new predicate" in
     Some newd
	
  let combineSuccessors ((succ1,vars1):t) ((succ2,vars2):t) :t = 
    match succ1.pred_content,succ2.pred_content with 
      Pfalse, _ -> (succ2,vars2)
    | _, Pfalse -> (succ1,vars1)
    | _,_ -> 
      let remove_doubles l1 l2 = 
	let set = 
	  List.fold_left
	    (fun acc l_v -> 
	      Logic_var.Set.add l_v acc)
	    (Logic_var.Set.of_list l1)
	    l2
	in
	Logic_var.Set.elements set
      in
      (unamed (Por (succ1,succ2)))
	,
      (remove_doubles vars1 vars2)

  let rec treat_if cond_exp b1 b2 = (* -> prefix * wp(B,T) * wlp (B,\bot) *)
    
    let old_binds = 
      !var_map
    (* As we modify the map in the then part, we need to 
       remeber the old bindings to use them in the else part. *)
	
    in
    let var_changed = 
      
      List.fold_left
	(fun acc st -> 
	  match st.skind with
	    Instr (Set ((Var v,_), _, _)) 
	  | Instr (Call ((Some (Var v,_)),_,_,_))
	    -> 
	    Varinfo.Set.add v acc
	  | _ -> acc 
	)
	Varinfo.Set.empty
	(b1.bstmts @ b2.bstmts)
    in
    (*let var_no_double = Varinfo.Set.elements var_changed
    in
    *)
    let treat_block block = 
      let () = 
	Mat_option.debug ~dkey:dkey_stmt ~level:4
	  "Block treated : @[%a@]"
	  Printer.pp_block block in
      let stmt_action stmt (wp : predicate option) = 
	let in_good_if =
	  begin
	    match (fst(Stmt.Hashtbl.find if_stmt_hashtbl stmt)).skind
	    with
	      If (e,_,_,_) -> 
		Exp.equal e cond_exp
	    | _ -> assert false
	  end
	in
	if (not in_good_if)
	then (wp(* ,wlp *)) 
	else 
	  match stmt.skind with
	    If (e,b1,b2,_) -> 
	      let pref,wp_top(* ,wlp_bot *) = treat_if e b1 b2
	      in

	      let wp_part = 
		Pimplies 
		  ( unamed pref,
		    unamed wp_top(* wp_part *) )
	      in
	      
	      Some (unamed wp_part) (* , wlp_part *)
        
	  | Instr i ->
	    begin
	      match i with 
		Set ((Var v,_), exp, _) -> 
		  
		    (*let () = 
		      var_used := Varinfo.Set.add v !var_used
		      
		      in*)
		  let actual_var = get_lvar v
		  in
		  
		    
		  let lval_term = 
		    tvar actual_var
		  in
		  
		  let () = 
		    if stmt.preds <> []
		    then
		      ignore (get_new_lvar v)
		  in
		  
		  let correct_term = correct_term_from_exp exp 
		  in
		  
		  
		  let new_pred = 
		  Prel (Req, lval_term, correct_term)
		      
		      
		  in
		  if wp = None then Some (unamed new_pred)
		  else 
		    Some (unamed(Pimplies
			    (unamed new_pred,
			     ((Extlib.the wp)))))(* , *)
		      
		     (* (Pimplies *)
		(* 	(new_pred, *)
		(* 	 (unamed wlp)))) *)
		      
	      | _ -> (wp(* ,wlp *))(* todo : treat the rest *)
	    end
	      
	  | Return _ 
	  | Goto _
	  | Break _
	  | Continue _
	  | Block _
	  | UnspecifiedSequence _
	  | Throw _
	  | TryCatch _
	  | TryFinally _
	  | TryExcept _ -> (wp(* ,wlp *))
	    
	  | Switch _ -> assert false	
	    
	  | Loop (_,_,_,_,_) -> assert false
	    
      in
      
      
      let rec wp_block s_list wp : Cil_types.predicate option =
	match s_list with
	  [] -> Some (unamed Ptrue)
	| hd :: [] -> 
	  let () = 
	    Mat_option.debug ~dkey:dkey_stmt ~level:3
	      "Last statement treated : @[%a@]"
	      Printer.pp_stmt 
	      hd
	  in
	  (stmt_action
	     hd
	     None)
	| hd :: tl -> 
	  
	  let () = 
	    Mat_option.debug ~dkey:dkey_stmt ~level:3
	      "Statement treated : @[%a@]"
	      Printer.pp_stmt 
	      hd;
	    match wp with
	      None -> 
		Mat_option.debug ~dkey:dkey_stmt ~level:3
		  "No current predicate"
	    | Some p -> 
		Mat_option.debug ~dkey:dkey_stmt ~level:3
		  "Current predicate : %a" Printer.pp_predicate p
	  in
	  (stmt_action 
	     hd 
	     (wp_block 
		tl
		wp))
	    
      (*List.fold_right
	(fun stmt (wp(*, wlp *)) -> *)
      in
      match wp_block block.bstmts None with
	None -> unamed Ptrue
      | Some p -> p
    in
    
    let () = 
      Mat_option.debug ~dkey:dkey_stmt ~level:2
	"Then block treated"
    in
    let then_wp(* ,then_wlp *) = treat_block b1
    in
    
    let then_binds = !var_map
    in
    
    let () =  
      Varinfo.Map.iter
	(fun v lv -> 
	  Mat_option.debug 
	    "Old : @[%a@] -> @[%a@]"
	    Printer.pp_varinfo v
	    Printer.pp_logic_var lv
	)
	old_binds
      ;
      
      Varinfo.Map.iter
	(fun v lv -> 
	  Mat_option.debug 
	    "Then : @[%a@] -> @[%a@]"
	    Printer.pp_varinfo v
	    Printer.pp_logic_var lv
	)
	then_binds
	
	
    in
    let () = var_map := old_binds
    in
    let () = 
      Mat_option.debug ~dkey:dkey_stmt ~level:2
	"Else block treated"
    in
    let else_wp(* ,else_wlp *) =
      let form = treat_block b2 in 
      (* If nothing happened in the else block, we need to update the variables
	 used in the then path *)
      if form.pred_content = Ptrue
      then (* var_map have not been modified, we will continue with the 
	      then_map as var_map *)
	let () = var_map := then_binds in
	Varinfo.Map.fold
	  (fun var lvar acc ->
	    
	    try 
	      let old_var = 
		Varinfo.Map.find var old_binds
	      in
	      let eqlty = 
		Prel 
		  (Req, 
		   (Logic_const.tvar old_var), 
		   (Logic_const.tvar lvar))
		  
	      in
	      if acc = Ptrue then eqlty
	      else Pand (unamed eqlty, unamed acc)
	    with
	      Not_found ->acc
		
		
	  )
	  then_binds
	  form.pred_content
      else form.pred_content

    (* We now unify the variable out from the then part and the else part *)
      
    in
    let term_of_cond = correct_term_from_exp cond_exp
    in
    
    let () = 
      Mat_option.debug
	"term of condition = @[%a@]" Printer.pp_term term_of_cond
    in
    let cond_satisfied = 
      unamed (
	Pif
	  (term_of_cond, unamed Ptrue, unamed Pfalse))
    in
    let cond_unsatisfied = 
      unamed
	(Pnot cond_satisfied)
    in
    
    let then_wp(* ,then_wlp *) = 
      Pimplies
	(cond_satisfied, (then_wp))(* , *)
      (* Pimplies  *)
      (* 	(cond_satisfied, (unamed then_wlp)) *)
    in
    let else_wp(* ,else_wlp *) =	
      Pimplies 
	(cond_unsatisfied, (unamed else_wp))(* , *)
      (* Pimplies  *)
      (* 	(cond_unsatisfied, (unamed else_wlp)) *)
    in
    
    let wp_form =
      Pand
	((unamed then_wp),
	 (unamed else_wp))
    in
    (* let wlp_form = *)
    (*   Pand *)
    (* 	((unamed then_wlp), *)
    (* 	 (unamed else_wlp)) *)
    (* in *)
    let map_of_varinfos =
      Varinfo.Set.fold
	(fun v acc_then -> 
	  
	  let new_var = 
	    get_lvar v
	  in 
	  
	  try 
	    let then_v = Varinfo.Map.find v then_binds
	    in
	    let then_mapping = 
	      Prel 
		(Req, 
		 (Logic_const.tvar new_var), 
		 (Logic_const.tvar then_v))
		
	    in
	  (then_mapping :: acc_then)
	  with 
	    Not_found -> (* then_v failed, as a new variable has been seen in 
			    else only. In this case, we don't need to talk 
			    about this variable in the then case*) 
	      acc_then
	      
	)
        var_changed
	[]
    in
    let bind_prefix = 
      match map_of_varinfos with
	[] -> wp_form
      | hd :: tl ->
	List.fold_left
	  (fun acc_form bind -> 
	    Pand 
	      (
		(unamed bind),
		(unamed acc_form)
	      )
	  )
	  hd
	  tl
    in
    
    (bind_prefix,wp_form(* ,wlp_form *))
      
  let loop_as_predicate kf loop_stmt b so = 
    
    (* First, we get the condition as a predicate over the actual variables. *)
    
    let loop_cond = 
      let () = 
	Mat_option.debug ~dkey:dkey_stmt ~level:2
	  "Loop. Exit statement = @[%a@].\nPreds ="
	  Printer.pp_stmt
	  (Extlib.the so)
      in
      let () = 
	List.iter
	  (fun s -> 
	    Mat_option.debug ~dkey:dkey_stmt ~level:2
	      "@[%a@]"
	      Printer.pp_stmt
	      s)
	  
	  (Extlib.the so).succs
      in
      
      let if_stmts = 
        (Extlib.the so).succs
      in 
      if_conds_as_pred if_stmts
	
    (* Then, we get proven annotations *)
    in
    let annot_pred = 
      List.fold_left
	(fun (acc:predicate) annot ->
	  match annot.annot_content with
	    AInvariant (_,_,pred) -> 
	      let status = Property_status.get 
		(Property.ip_of_code_annot_single kf loop_stmt annot) 
	      in begin 
	      match status with
		Property_status.Best (Property_status.True,_) -> 
		  if acc.pred_content = Ptrue 
		  then pred
		  else unamed (Pand (acc,pred))
	      | _ -> acc
	      end 
	  | _ -> acc
	)
	(unamed Ptrue)
	(Annotations.code_annot loop_stmt)
    
	
    (* Then, we treat the loop *)
    in
    let res = 
      try 
	unamed (Pand ( unamed(loop_to_the_n b loop_cond), annot_pred)) with
	  Not_a_simple_loop -> annot_pred
	| _ -> Mat_option.feedback "Error during matrix study, skip."; annot_pred
    in
    let () = 
      Mat_option.debug ~level:3
	"Loop treatment done. Predicate : %a"
	Printer.pp_predicate res
    in 
    res
    
  let doStmt s = 
    let () = 
      Mat_option.debug ~dkey:dkey_stmt "Statement treated : @[%a@]"
	Printer.pp_stmt
	s
    in
    if Stmt.Set.mem s !treated_stmt
    then 
    (* We already treated this one, we will not treat it again *)
      let () = 
	Mat_option.debug ~dkey:dkey_stmt "Statement previously treated"
      in
      Done (StmtStartData.find s)
    else
      let find_prev_data s = 
	let rec __find_prev_data (pred_acc, var_acc) succs = 
	  try 
	    let pred,old_vars =  
	      StmtStartData.find (List.hd succs)
	    in
	    if pred.pred_content = Ptrue 
	    then __find_prev_data (pred_acc,var_acc) (List.tl succs)
	    else
	      let pred_acc =
		if pred_acc.pred_content = Pfalse then pred else
		  unamed
		    (Por
		       ((pred_acc),
			(pred)))
	      in
	      let var_acc = 
		old_vars @ var_acc
	      in
	      __find_prev_data 
		
		(pred_acc,var_acc)
		(List.tl succs)
	  with 
	  | Not_found -> __find_prev_data (pred_acc, var_acc) (List.tl succs)
	  | Failure s (*"hd"*) -> assert (s = "hd"); (pred_acc, var_acc)
	in
	__find_prev_data 
	  (unamed Pfalse,[]) s.succs
      in
      let prev_data,vars = 
	find_prev_data s
    (* result is useless, as we will not use it. This failure happens when we 
       start the analysis  *)
      in
      let remove_doubles l = 
	Logic_var.Set.elements (Logic_var.Set.of_list l)
      in   
      
      let real_vars = remove_doubles vars 
      in
      let () = 
	if not (StmtStartData.mem s)
	then 
	  let () = 
	    Mat_option.debug 
	      ~dkey:dkey_stmt 
	      "Not registered"
	  in
	  StmtStartData.add s (prev_data,real_vars)
	else
	  Mat_option.debug 
	    ~dkey:dkey_stmt 
	    "Registered"
      in
      
      if Stmt.Hashtbl.mem if_stmt_hashtbl s || Stmt.Hashtbl.mem loop_hashtbl s
      then 
	Done (prev_data,real_vars)
      else
	match s.skind with
	  Instr _
	| Return _
	| Goto _
	| Break _
	| Continue _
	| Block _
	| UnspecifiedSequence _
	| Throw _
	| TryCatch _
	| TryFinally _
	| TryExcept _ ->  
	  Default
	    
	| If (exp,b1,b2,_) -> 	
	  
          let prev_calculated_pred,_ = 
	    try
	      CafeStartData.find (List.hd s.succs)
	    with
	      Not_found -> 
		Mat_option.fatal
		  "@[%a@] has not been found in registered statements."
		  Printer.pp_stmt 
		  s
	  in
	  let bind_prefix,wp(* ,wlp *) = treat_if exp b1 b2
	  in
	  let form = 
	    
	    Pand
	      ((unamed wp),
	       (prev_calculated_pred))
	(* Pand  *)
	(*   ((unamed wp), *)
	(*   (unamed ( *)
	(*     Por(  *)
	(* 	(unamed wlp), *)
	(* 	(unamed prev_calculated_pred))))) *)
	  in
	  
	  let form = 
	    Pand (unamed bind_prefix, unamed form) 
	  in
	  let actual_vars = 
	    Varinfo.Map.fold
	      (fun _ lv acc -> lv :: acc)
	      !var_map
	      []
	  in
	  Done (unamed form,actual_vars)
	    
	| Switch _ -> assert false
	  
	| Loop (_,b,_,_,so) -> 
	  let if_stmt = 
	    List.hd (Extlib.the so).succs
	  in
	  (*let _,old_vars = 
	    try
	      CafeStartData.find (List.hd s.succs)
	    with
	      Not_found -> 
		Mat_option.fatal
		  "Loop head @[%a@] not registered"
		  Printer.pp_stmt 
		  s
	  in*)
	  let () = (* We compute the condition as a predicate just to visit the
		      condition and register every varinfo in it. *)
	    ignore (if_conds_as_pred [if_stmt])
	  in(*
	  let old_vars = 
	    Varinfo.Map.fold
	      (fun _ lv acc -> 
		if List.exists (Logic_var.equal lv) acc then acc else lv :: acc)
	      !var_map
	      old_vars
	  in*)
	  
	  let pred = loop_as_predicate (Kernel_function.find_englobing_kf s) s b so

	(* pred represents at least one step of the loop. We
	   need to specify the case "loop not taken".*)


	in
(*	let uniformize_pred = 
	  uniformize 
	    old_vars 
	in
*)	let new_vars = 
	  Varinfo.Map.fold
	    (fun _ lv acc -> lv :: acc)
	    !var_map
	    []
	    
	in
	  
	let loop_cond = 
	  if_conds_as_pred [if_stmt]
	in
	let no_loop_pred = 
	  Pnot (loop_cond)
	in
	
	let rec update_block_vars b = 
	  List.iter
	    (fun s ->
	      (*Mat_option.debug ~dkey:dkey_stmt ~level:3 
		"Statement %a registered as treated" Printer.pp_stmt s;
	      treated_stmt := Stmt.Set.add s !treated_stmt;
	      StmtStartData.add s data;
	      *)
	      match s.skind with 
		Block b -> update_block_vars b
	      | Instr(Set ((Var v,_),_,_)) -> ignore (get_new_lvar v)
	      | _ -> ()
	    ) b.bstmts in
	

	let () = update_block_vars b in


	let data = 
	unamed(Pand (unamed no_loop_pred,pred))
		 ,new_vars
	in
	let rec register_block_stmt (b : Cil_types.block) =
	    List.iter 
	      (fun s ->
		Mat_option.debug ~dkey:dkey_stmt ~level:3 
		  "Statement %a registered as treated" Printer.pp_stmt s;
		treated_stmt := Stmt.Set.add s !treated_stmt;
		StmtStartData.add s data;
		match s.skind with 
		  Block b -> register_block_stmt b
		| _ -> ()
	      ) b.bstmts in
	
	let () = (* register loop statement as treated *)
	    register_block_stmt b
	in 
	
        
	Done data

  let doInstr _ i ((pred,vars):t) =
    match i with
      Call _ 
    | Asm _ 
    | Skip _ -> Default
      
    | Code_annot _ -> Default 
      (* todo : 
	 - if proved, get results 
	 - treat assertions *)
      
    | Set ((lhost,_),exp,_) ->
      match lhost with 
	Var v -> 
	  let () = Mat_option.debug "Set : correcting the predicate" in
	  Done ((update_pred_about_var v exp pred.pred_content),vars)
      | Mem _ -> Default (* todo : treat tab *)
	
  let filterStmt _ _ = true
    
end
  
module Cafe_Backward (Pred : P) = Backwards (Efac (Pred))

let block_registerer () = 
object
  inherit Visitor.frama_c_inplace

  method! vstmt_aux s = 
    match s.skind with
      If (_, b1, b2, _) -> 
	update_table s b1.bstmts b2.bstmts; DoChildren
    | Loop (_,b,_,_,_) -> 
      update_loop_table s b.bstmts; DoChildren
    | _ -> DoChildren
end