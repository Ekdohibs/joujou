open Lexing

type place =
  position * position

let place lexbuf : place =
  lexbuf.lex_start_p, lexbuf.lex_curr_p

let line p : int =
  p.pos_lnum

let column p : int =
  p.pos_cnum - p.pos_bol

let show place : string =
  let startp, endp = place in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d"
    startp.pos_fname
    (line startp)
    (column startp)
    (endp.pos_cnum - startp.pos_bol) (* intentionally [startp.pos_bol] *)

let display continuation header place format =
  Printf.fprintf stderr "%s:\n" (show place);
  Printf.kfprintf
    continuation
    stderr
    (header ^^ format ^^ "\n%!")

let error place format =
  display
    (fun _ -> exit 1)
    "Error: "
    place format

let set_filename lexbuf filename =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename }

let pp_place formatter _place =
  Format.fprintf formatter "<>"
