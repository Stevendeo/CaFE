include Plugin.S

module Enabled: Parameter_sig.Bool

module Formula_file: Parameter_sig.String

module Auto_gen: Parameter_sig.Bool
module Simplify: Parameter_sig.Int

module Ignore_fun: Parameter_sig.String
module Assert_annot : Parameter_sig.Bool

module Create_res: Parameter_sig.Bool
module Output_res: Parameter_sig.String

module Dot: Parameter_sig.Bool
module Output_dot: Parameter_sig.String

module Output_closure : Parameter_sig.String
module Closure: Parameter_sig.Bool

module Output_atoms : Parameter_sig.String
module Atoms: Parameter_sig.Bool

module Complete_states : Parameter_sig.String

module All_paths: Parameter_sig.Bool
module Only_main: Parameter_sig.Bool
module Main_ends: Parameter_sig.Bool

module Atom_simp: Parameter_sig.Bool

module Call_print: Parameter_sig.Bool

module Spurious: Parameter_sig.Bool

module Print_memo: Parameter_sig.Bool

module Unreachable_states: Parameter_sig.Bool
