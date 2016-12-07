open Caretast

module Caret_Formula = 
  Datatype.Make
    (struct 
      type t = caret_formula
      
      let name = "Caret_formula"
      let reprs = [CTrue]
	
      let rec equal (f1:t) (f2:t) = 
	
	match f1,f2 with
	  CNext (o,n1), CNext (o2,n2)
	| CFatally (o,n1), CFatally (o2,n2) 
	| CGlobally (o,n1), CGlobally (o2,n2) 
	  -> o = o2 && equal n1 n2

	| CUntil (o,n11,n12), CUntil (o2,n21,n22) 
	  -> o = o2 && equal n11 n21 && equal n12 n22

	| CNot n1, CNot n2 
	  -> equal n1 n2
	  
	| CAnd (n11, n12), CAnd (n21, n22)
	| COr (n11, n12), COr (n21, n22)
	| CImplies (n11, n12), CImplies (n21, n22)
	| CIff (n11, n12), CIff (n21, n22) -> equal n11 n21 && equal n12 n22
	| CProp(p,_), CProp(p2,_) 
	  -> Cil_datatype.Identified_predicate.equal p p2
	| CInfo i_p1, CInfo i_p2 -> i_p1 = i_p2 
	
	| _,_ -> f1 = f2


      let mem_project = Datatype.never_any_project
	
      let varname formula = 
	let printOpKind = function
	  | General -> "N "
	  | Abstract -> "A "
	  | Past -> "P "
	in
	let printInfo = function
	  | ICall (Some s) -> "Call_" ^ s 
	  | ICall _ -> "Call"
	  | IRet (Some s) -> "Ret_" ^ s
	  | IRet _ -> "Ret"
	  |Caretast.IInt  -> "Int"
	in
	let rec stringOf =  function
	
	  | CNext (op,f) -> "( X"^ (printOpKind op) ^ (stringOf f) ^" )"
	  | CUntil (op, f1 ,f2) -> 
	    "( " ^(stringOf f1) ^ " U" ^(printOpKind op) ^ (stringOf f2) ^" )"
	  | CFatally (op,f) -> "( F"^ (printOpKind op) ^ (stringOf f) ^" )"
	  | CGlobally(op,f) -> "( G"^ (printOpKind op) ^ (stringOf f) ^" )"
	  | CNot f -> "NOT\\(" ^  (stringOf f) ^ "\\)" (* Todo : delete the \ *)
	  | CAnd (f1 ,f2) ->"( "^ (stringOf f1) ^ " & " ^ (stringOf f2) ^" )"
	  | COr (f1, f2)-> "( "^ (stringOf f1) ^ " | " ^ (stringOf f2) ^" )"
	  | CImplies (f1, f2)-> "( "^ (stringOf f1) ^ " => " ^ (stringOf f2) ^" )"
	  | CIff (f1, f2)-> "( "^ (stringOf f1) ^ " <=> " ^ (stringOf f2) ^" )"  
	  | CTrue -> "TRUE"
	  | CFalse -> "FALSE"
	  | CProp (_,str) -> str
	    
	  | CInfo i -> printInfo i
	    
	in
	(stringOf formula)
	  
	  
      let pretty fmt p = 
	match p with
	  CProp (p,_) -> Cil_datatype.Identified_predicate.pretty fmt p
	| _ -> Format.fprintf fmt "%s" (varname p)

      let copy f = f
      let internal_pretty_code _ = assert false
      let hash _ = assert false
      let compare _ = assert false
      let rehash = hash
      let structural_descr = Structural_descr.t_abstract
     end)


module Id_Formula = 
  Datatype.Make_with_collections
    (struct
      type t = Caretast.identified_formula
      include Datatype.Undefined
      let name = "Identified_formula"
      let reprs = 
	[{ 
	  f_id = -1;
	  form = CTrue
	 }]

      let equal (f1:t) (f2:t) = 
 (*        let f1 = f1.form in 
	let f2 = f2.form in
 *)
	f1.f_id = f2.f_id(* || (Caret_Formula.equal f1 f2)*)


      let compare (f1:t) (f2:t) = Pervasives.compare f1.f_id f2.f_id
      let hash (x:t) = x.f_id
      let copy = Datatype.identity
      let rehash = Datatype.identity
      let mem_project = Datatype.never_any_project
	
      let varname (f:t) = Caret_Formula.varname f.form	

      let pretty fmt p = Caret_Formula.pretty fmt p.form
       end)
