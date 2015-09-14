{
  open Lexing
  open Formula_parser
  
  let loc lexbuf = (lexeme_start_p lexbuf, lexeme_end_p lexbuf)
    
  let buf = Buffer.create 1024
    
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
  exception Error of(Lexing.position * Lexing.position) * string

  let raise_located loc e = raise (Error (loc, e)) 
}

let autChr = ['a'-'z' 'A'-'Z' '_' '<' '>' '=' '0'-'9' '+' '-' '*' '/' '\\' '&' '|' '!' '%' '^' '[' ']' '(' ')' '.']

let spaces = [' ' '\t' '\n']
rule token = parse

  	| spaces { token lexbuf }
	| eof {EOF}
	
	| "True"   	{ TRUE }
	| "False"   	{ FALSE }
	| "Call{" ((autChr| spaces)* as str) '}' { CALL(str) } 
	| "Ret{" ((autChr| spaces)* as str) '}' { RETURN(str) }

	| '{' (autChr | spaces)+ '}' as str {PROP(str)}

	| '('	  	{ L_PAREN }
	| ')'	  	{ R_PAREN }

(* Operator kinds *)
	| "@N"		{GENERAL}	
	| "@A"		{ABSTRACT}
	| "@P"		{PAST}

(* Logic operators *)
	| "==>"		{ IMPLIES }
	| "<=>"		{ EQUIV }
	| "OR"	 	{ OR }
	| "AND"	 	{ AND }
	| '!'	  	{ NOT }

(* CaRet operators *)
	| 'G'		{ GLOBALLY }
	| 'F'		{ FATALLY }
	| 'U'		{ UNTIL }
	| 'X'		{ NEXT }

	| _  {
	  raise_located 
		(loc lexbuf)
          	(Format.sprintf "Illegal_character %s" (lexeme lexbuf))
    }

(*         {
	  raise_located 
		(loc lexbuf)
          	(Format.sprintf "Illegal_character %s\n" (lexeme lexbuf))
    }*)

{

let parse c = 
	let lb = Lexing.from_channel c in
	try 
		Formula_parser.main token lb
    	with
          Invalid_argument _
	| Parsing.Parse_error -> raise_located (loc lb) "Syntax error"
}
