(* open Cil_types *)

(** CaRet formula parsed abstract syntax trees *)

type pred =  Cil_types.predicate

type op_kind = 
  |General  (** Operator LTL-like  *)
  |Abstract (** Operator CALL to RETURN *)
  |Past     (** From somewhere to the matching call *)

type info_prop = 
  |ICall of string option 
  (** Denotes the invocation of a module  *)

  |IRet of string option
  (** Denotes the exit or the return of a module  *)

  |IInt  

type caret_formula =
  (** 'Next' temporal operator *)
  | CNext of op_kind * caret_formula   
       
  (** 'Until' temporal operator *)
  | CUntil of op_kind * caret_formula * caret_formula 

  (** 'Fatally' temporal operator *)
  | CFatally of op_kind * caret_formula       

  (** 'Globally' temporal operator *)
  | CGlobally of op_kind * caret_formula              

  | CNot of caret_formula                     (** 'not' logic operator *)
  | CAnd of caret_formula * caret_formula     (** 'and' logic operator *)
  | COr of caret_formula * caret_formula      (** 'or' logic operator *)
  | CImplies of caret_formula * caret_formula (** '=>' logic operator *)
  | CIff of caret_formula * caret_formula     (** '<=>' logic operator *)

  | CTrue  (** 'true' logic constant *)
  | CFalse (** 'false' logic constant *)

  | CProp of pred * string (** Denotes an atomic predicate *)
  | CInfo of info_prop     (** Designs a CaRet proposition
			       (call, return ou intern) *)

type identified_formula = 
  {
    f_id : int;
    mutable form : caret_formula
  }
