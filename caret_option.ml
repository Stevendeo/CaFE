include Plugin.Register
  (struct
    let name ="CaRet for Frama-C"
    let shortname = "cafe"
    let help = "model checking with CaRet formulas"
   end)

module Enabled = False
  (struct 
    let option_name = "-cafe"
    let help = "when on (off by default), model checking with CaRet formulas" 
   end)

module Formula_file = String
  (struct
    let option_name = "-cafe-formula"
    let arg_name = "caret-formula"
    let default = ""
    let help = 
      "file in which the formula is written." 
   end)

module Auto_gen = True
    (struct 
    let option_name = "-cafe-auto"
    let help = "when on (on by default), generates the automaton. Desactivate only for debug"
   end)

module Create_res = True
  (struct 
    let option_name = "-cafe-work"
    let help = "when on (on by default), tells you if your program doesn't satisfy your CaRet property. Desactivate only for debug"
   end)

module Output_res = String
  (struct 
    let option_name = "-cafe-output"
    let default = ""
    let arg_name = "output-file"
    let help = 
      "file where the result is output (default : console)"
   end)

module Simplify = Int
  (struct 
    let option_name = "-cafe-simp-level"
    let default = 2
    let arg_name = "n"
    let help = 
      "level of simplification : 0 for nothing ; 1 for deleting"
      ^ " unreachable states ; 2 for deleting dead-end states ; "
      ^ "3 for complete simplification (2 by default) " 
   end)

module Ignore_fun = String
  (struct 
    let option_name = "-fignore"
    let default = ""
    let arg_name = "<f1;...>"
    let help = 
      "List of the functions ignored by the analysis"
   end)

module Assert_annot = True
  (struct
    let option_name = "-cafe-assert"
    let help = "when on (on by default), considers loop invariants as true"
   end)

module Output_dot = String
  (struct 
    let option_name = "-cafe-dot-output"
    let default = ""
    let arg_name = "output-file"
    let help = 
      "file where the automaton, as a dot file, is output (default : console)"
   end)

module Dot = False
  (struct
    let option_name = "-cafe-dot"
    let help = "when on (off by default), generates the dot representation of the automaton. When off, generates some informations about the automaton."
   end)

module Output_closure = String
  (struct 
    let option_name = "-cafe-closure-output"
    let default = ""
    let arg_name = "output-file"
    let help = 
      "file where the formula closure is output (default : console)"
   end)


module Closure = False
  (struct
    let option_name = "-cafe-closure"
    let help = 
      "generates a file containing the closure set of the formula in argument"
   end)

module Output_atoms = String
  (struct 
    let option_name = "-cafe-atoms-output"
    let default = ""
    let arg_name = "output-file"
    let help = 
      "file where the set of atoms from the formula is output (default : console)"
   end)
  
module Atoms = False
  (struct
    let option_name = "-cafe-atoms"
    let help = "generates a file containing the atoms of the formula"
   end)


module Complete_states = String
  (struct 
    let option_name = "-cafe-states"
    let default = ""
    let arg_name = "output-file"
    let help = "in this file will be found every information about each state"
   end)

module All_paths = False
  (struct
    let option_name = "-cafe-all"
    let help = "when on (off by default) generates all paths that doesnt satisfy the formula. When off, just one. "
   end)

module Only_main = True
    (struct
    let option_name = "-cafe-main"
    let help = "when on (on by default), only checks the first loop encourntered in the main.c file. Infinite paths on other functions are not considered."
   end)

module Main_ends = True
    (struct
    let option_name = "-cafe-end"
    let help = "when on (on by default), considers the c program ends eventually in any case."
   end)

module Atom_simp = True
  (
    struct
      let option_name = "-atom-simp"
      let help = "when on (on by default), tries to delete self-inconsistent atoms. Uses CVC3."
    end )

module Call_print = True
  (
    struct
      let option_name = "-pretty-call"
      let help = "when on (on by default), only prints the call path of the main function. When off, prints the whole counter example path. "
    end )


module Spurious = False
  (
    struct
      let option_name = "-spurious"
      let help = "when on (off by default), prints the list of statement where formulas were found spurious"
    end )

module Print_memo = False
      (
    struct
      let option_name = "-memoizer"
      let help = "undocumented"
    end )


module Unreachable_states = False
      (
    struct
      let option_name = "-cafe-unr"
      let help = "when on (on by default),\
                  considers value is right when it says a state is unreachable. "
    end )
