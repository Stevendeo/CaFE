type token =
  | PROP of (string)
  | TRUE
  | FALSE
  | INTERN
  | CALL of (string)
  | RETURN of (string)
  | NEXT
  | FATALLY
  | GLOBALLY
  | NOT
  | UNTIL
  | OR
  | AND
  | IMPLIES
  | EQUIV
  | GENERAL
  | ABSTRACT
  | PAST
  | L_PAREN
  | R_PAREN
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Caretast.caret_formula
