FRAMAC_SHARE 	?=$(shell frama-c.byte -print-path)
FRAMAC_LIBDIR 	?=$(shell frama-c.byte -print-libpath)

PLUGIN_DIR ?=.
PLUGIN_NAME 	= CaRet

PLUGIN_GENERATED := $(addprefix ${PLUGIN_DIR}/, \
		formula_parser.ml formula_parser.mli)

PLUGIN_CMI	:= caretast 

PLUGIN_CMO 	:= zipper \
	caret_option \
	formula_datatype \
	atoms \
	rsmast \
	atoms_utils \
	caret_print \
	smt_solver \
	formula_typer \
	formula_parser \
	formula_lexer \
	formula_utils \
	counter_example \
	rsm \
	caret_visitor \
	caret
PLUGIN_HAS_MLI	:= yes
PLUGIN_NO_TEST:=yes
PLUGIN_DISTRIBUTED:=yes
include $(FRAMAC_SHARE)/Makefile.dynamic
