include Plugin.Register
  (struct
    let name ="model_caret"
    let shortname = "caret"
    let help = "model checking with CaRet formulas"
   end)

module Enabled = False
  (struct 
    let option_name = "-caret"
    let help = "when on (off by default), model checking with CaRet formulas" 
   end)

module Formula_file = String
  (struct
    let option_name = "-caret-formula"
    let arg_name = "caret-formula"
    let default = ""
    let help = 
      "file in which the formula is written." 
   end)

module Auto_gen = True
    (struct 
    let option_name = "-caret-auto"
    let help = "when on (on by default), generates the automaton. Desactivate only for debug"
   end)

module Create_res = True
  (struct 
    let option_name = "-caret-work"
    let help = "when on (on by default), tells you if your program doesn't satisfy your CaRet property. Desactivate only for debug"
   end)

module Output_res = String
  (struct 
    let option_name = "-caret-output"
    let default = ""
    let arg_name = "output-file"
    let help = 
      "file where the result is output (default : console)"
   end)

module Simplify = Int
  (struct 
    let option_name = "-caret-simp-level"
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

module Output_dot = String
  (struct 
    let option_name = "-caret-dot-output"
    let default = ""
    let arg_name = "output-file"
    let help = 
      "file where the automaton, as a dot file, is output (default : console)"
   end)

module Dot = False
  (struct
    let option_name = "-caret-dot"
    let help = "when on (off by default), generates the dot representation of the automaton. When off, generates some informations about the automaton."
   end)

module Output_closure = String
  (struct 
    let option_name = "-caret-closure-output"
    let default = ""
    let arg_name = "output-file"
    let help = 
      "file where the formula closure is output (default : console)"
   end)


module Closure = False
  (struct
    let option_name = "-caret-closure"
    let help = 
      "generates a file containing the closure set of the formula in argument"
   end)

module Output_atoms = String
  (struct 
    let option_name = "-caret-atoms-output"
    let default = ""
    let arg_name = "output-file"
    let help = 
      "file where the set of atoms from the formula is output (default : console)"
   end)
  
module Atoms = False
  (struct
    let option_name = "-caret-atoms"
    let help = "generates a file containing the atoms of the formula"
   end)


module Complete_states = String
  (struct 
    let option_name = "-caret-states"
    let default = ""
    let arg_name = "output-file"
    let help = "in this file will be found every information about each state"
   end)

module All_paths = False
  (struct
    let option_name = "-caret-all"
    let help = "when on (off by default) generates all paths that doesnt satisfy the formula. When off, just one. "
   end)

module Only_main = True
    (struct
    let option_name = "-caret-main"
    let help = "when on (on by default), only checks the first loop encourntered in the main.c file. Infinite paths on other functions are not considered."
   end)

module Main_ends = True
    (struct
    let option_name = "-caret-end"
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

module Ceana = False
    (
    struct
      let option_name = "-ceana"
      let help = "when on (on by default), applies a counter example analysis"
    end )

module Print_Cegar = False
    (
    struct
      let option_name = "-cegar-print"
      let help = "when on (off by default), prints the content of the registered Value states in the counter example analysis hook."
    end )

module Print_memo = False
      (
    struct
      let option_name = "-memoizer"
      let help = "undocumented"
    end )
