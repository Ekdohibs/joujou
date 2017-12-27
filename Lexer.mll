{

open Lexing
open Error
open Parser
open RawLambda

let kw = [
  "callcc", CALLCC ;
  "else", ELSE ;
  "fun", FUN ;
  "ifzero", IFZERO ;
  "in", IN ;
  "let", LET ;
  "match", MATCH ;
  "of", OF ;
  "print", PRINT ;
  "rec", REC ;
  "then", THEN ;
  "type", TYPE ;
  "with", WITH ;
]

let keywords = Hashtbl.create (List.length kw)
let () = List.iter (fun (a,b) -> Hashtbl.add keywords a b) kw

}

(* -------------------------------------------------------------------------- *)

(* Regular expressions. *)

let newline =
  ('\010' | '\013' | "\013\010")

let whitespace =
  [ ' ' '\t' ]

let lowercase =
  ['a'-'z' '\223'-'\246' '\248'-'\255' '_']

let uppercase =
  ['A'-'Z' '\192'-'\214' '\216'-'\222']

let identchar =
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '0'-'9']

let digit =
  ['0'-'9']

(* -------------------------------------------------------------------------- *)

(* The lexer. *)

rule entry = parse
| "->"
    { ARROW }
| "="
    { EQ }
| "("
    { LPAREN }
| ")"
    { RPAREN }
| "+"
    { ADDOP OpAdd }
| "-"
    { ADDOP OpSub }
| "*"
    { MULOP OpMul }
| "/"
    { MULOP OpDiv }
| "|"
    { BAR }
| ","
    { COMMA }
| (lowercase identchar *) as x
    { try Hashtbl.find keywords x with Not_found -> IDENT x }
| (uppercase identchar *) as x
    { UIDENT x }
| digit+ as i
    { try
        INTLITERAL (int_of_string i)
      with Failure _ ->
        error (place lexbuf) "invalid integer literal." }
| "(*"
    { ocamlcomment (place lexbuf) lexbuf; entry lexbuf }
| newline
    { new_line lexbuf; entry lexbuf }
| whitespace+
    { entry lexbuf }
| eof
    { EOF }
| _ as c
    { error (place lexbuf) "unexpected character: '%c'." c }

(* ------------------------------------------------------------------------ *)

  (* Skip OCaml-style comments. Comments can be nested. This sub-lexer is
   parameterized with the place of the opening comment, so if an unterminated
   comment is detected, we can show where it was opened. *)

and ocamlcomment p = parse
| "*)"
    { () }
| "(*"
    { ocamlcomment (place lexbuf) lexbuf; ocamlcomment p lexbuf }
| newline
    { new_line lexbuf; ocamlcomment p lexbuf }
| eof
    { error p "unterminated comment." }
| _
    { ocamlcomment p lexbuf }
