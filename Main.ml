(* -------------------------------------------------------------------------- *)

(* Parse the command line. *)

let debug =
  ref false

let filenames =
  ref []

let record filename =
  filenames := filename :: !filenames

let options =
  Arg.align [
    "--debug", Arg.Set debug, " Enable debugging output";
  ]

let usage =
  Printf.sprintf "Usage: %s <options> <filename>" Sys.argv.(0)

let () =
  Arg.parse options record usage

let debug =
  !debug

let filenames =
  List.rev !filenames

(* -------------------------------------------------------------------------- *)

(* Printing a syntax tree in an intermediate language (for debugging). *)

let print_delimiter () =
  Printf.eprintf "----------------------------------------";
  Printf.eprintf "----------------------------------------\n"

let dump (phase : string) (show : 'term -> string) (t : 'term) =
  if debug then begin
    print_delimiter();
    Printf.eprintf "%s:\n\n%s\n\n%!" phase (show t)
  end;
  t

(* -------------------------------------------------------------------------- *)

(* Reading and parsing a file. *)

let read filename : RawLambda.term =
  try
    let contents = Utils.file_get_contents filename in
    let lexbuf = Lexing.from_string contents in
    Error.set_filename lexbuf filename;
    try
      Parser.entry Lexer.entry lexbuf
    with
    | Parser.Error ->
        Error.error (Error.place lexbuf) "Syntax error."
  with
  | Sys_error msg ->
      prerr_endline msg;
      exit 1

(* -------------------------------------------------------------------------- *)

(* Printing the final C program on the standard output channel. *)

let output (p : C.program) : unit =
  Printf.printf "#include<stdlib.h>\n";
  Printf.printf "#include<stdio.h>\n";
  Printf.printf "#include \"prologue.h\"\n\n";
  let print_program = PrintCommon.print_program PrintC.p_decl_or_function in
  let buf = Buffer.create 1024 in
  PrintCommon.printf_of_pprint_pretty print_program buf p;
  print_endline (Buffer.contents buf)

(* -------------------------------------------------------------------------- *)

(* The complete processing pipeline. Beautiful, isn't it? *)

let process filename =
  filename
  |> read
  |> dump "RawLambda" RawLambda.show_term
  |> Cook.cook_term
  |> dump "Lambda" Lambda.show_term
  |> CPS.cps_term
  |> dump "Tail" Tail.show_term
  |> Defun.defun_term
  |> dump "Top" Top.show_program
  |> Finish.finish_program
  |> dump "C" C.show_program
  |> output

(* -------------------------------------------------------------------------- *)

(* The main program. *)

let () =
  List.iter process filenames
