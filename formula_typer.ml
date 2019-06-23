open Cil
open Cil_types

exception Unbound of string

module Typer =
  Logic_typing.Make
    (struct
      let is_loop _ = false

      let anonCompFieldName =  Cabs2cil.anonCompFieldName
      let conditionalConversion = Cabs2cil.logicConditionalConversion

      let find_macro _ = raise Not_found
      let find_var ?label ~var =
	(* We search only for global vars or vars in the main func *)
	let good_var =
	  try
	    Globals.Vars.find_from_astinfo var VGlobal
	  with
	    Not_found ->
	    try
	      Globals.Vars.find_from_astinfo
		var
		(VLocal (Globals.Functions.find_by_name "main"))
	    with
	      Not_found ->
	      Caret_option.abort "Unbound variable %s" var
	in
        cvar_to_lvar good_var

      (* val find_enum_tag : string -> exp * typ *)
      let find_enum_tag str =
	try
	  Globals.Types.find_enum_tag str
	with Not_found ->
          Caret_option.abort "Unbound variable %s" str

      let find_type = Globals.Types.find_type

      let find_comp_field info s =

	let field = Cil.getCompField info s in
	Field(field,NoOffset)

      let find_label _ = raise Not_found

      let remove_logic_function _ = assert false
      let remove_logic_type _ = assert false
      let remove_logic_ctor _ = assert false
      let remove_logic_info _ = assert false

      let add_logic_function _ = assert false
      let add_logic_type _ _ = assert false
      let add_logic_ctor _ _ = assert false

      let find_all_logic_functions _ = raise Not_found
      let find_logic_type _ = raise Not_found
      let find_logic_ctor _ = raise Not_found

      let error _ _ = assert false
      let on_error f _g i = f i

      let integral_cast ty t =
	raise
          (Failure
             (Pretty_utils.sfprintf
		"term %a has type %a, but %a is expected."
		Printer.pp_term t Printer.pp_logic_type Linteger Printer.pp_typ ty))
     end)
