
(* The type of tokens. *)

type token = 
  | WITH
  | UNDERBAR
  | UID of (string)
  | TYPE
  | TUnit
  | TString
  | TRUE
  | TList
  | TInt
  | THEN
  | TBool
  | STRINGCONCAT
  | STRING of (string)
  | STRCON
  | STAR
  | SHOLE
  | SEMI
  | RPAREN
  | REC
  | RBRACKET
  | RBRACE
  | RAISE
  | PLUS
  | PIPE
  | OR
  | OF
  | NOTEQ
  | NOT
  | MOD
  | MINUS
  | MATCH
  | LPAREN
  | LISTTL
  | LISTSORT
  | LISTREVMAP
  | LISTREVAPD
  | LISTREV
  | LISTNTH
  | LISTMEMQ
  | LISTMEM
  | LISTMAPI
  | LISTMAP
  | LISTLENGTH
  | LISTHD
  | LISTFORALL
  | LISTFOLDR
  | LISTFOLDL
  | LISTFIND
  | LISTFILTER
  | LISTEXISTS
  | LISTASSOC
  | LISTAPPEND
  | LID of (string)
  | LET
  | LESSEQ
  | LESS
  | LBRACKET
  | LBRACE
  | LARGEREQ
  | LARGER
  | INT of (int)
  | IN
  | IF
  | IDENT
  | HOLE
  | FUNCTION
  | FUN
  | FATARR
  | FALSE
  | EXCEPTION
  | EQ
  | EOF
  | END
  | ELSE
  | DOUBLECOLON
  | DIVIDE
  | DEFAND
  | COMMA
  | COLON
  | BEGIN
  | AT
  | ARR
  | AND
  | AHOLE

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Lang.examples * Lang.prog)
