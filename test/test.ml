open Sys
open Array
open List
open Filename
open Printf
open Auxiliary

(* -------------------------------------------------------------------------- *)

(* Settings. *)

let create_expected =
  ref false

let verbosity =
  ref 0

let usage =
  sprintf "Usage: %s\n" argv.(0)

let spec = Arg.align [
  "--create-expected", Arg.Set create_expected,
                       " recreate the expected-output files";
  "--verbosity",       Arg.Int ((:=) verbosity),
                       " set the verbosity level (0-2)";
]

let () =
  Arg.parse spec (fun _ -> ()) usage

let create_expected =
  !create_expected

let verbosity =
  !verbosity

(* -------------------------------------------------------------------------- *)

(* Logging. *)

(* 0 is minimal verbosity;
   1 shows some progress messages;
   2 is maximal verbosity. *)

let log level format =
  kprintf (fun s ->
    if level <= verbosity then
      print_string s
  ) format

(* Extend [fail] to display an information message along the way.
   The message is immediately emitted by the worker, depending on
   the verbosity level, whereas the failure message is sent back
   to the master. *)

let fail id format =
  log 1 "[FAIL] %s\n%!" id;
  fail format

(* When issuing an external command, log it along the way. *)

let command cmd =
  log 2 "%s\n%!" cmd;
  command cmd

(* -------------------------------------------------------------------------- *)

(* Paths. *)

let root =
  absolute_directory ".."

let src =
  root

let good =
  root ^ "/tests"

let good_slash filename =
  good ^ "/" ^ filename

let joujou =
  src ^ "/joujou"

let gcc =
  sprintf "gcc -O2 -I %s" src

(* -------------------------------------------------------------------------- *)

(* Test files. *)

let thisfile =
  "this input file"

let lambda basename =
  basename ^ ".lambda"

(* -------------------------------------------------------------------------- *)

(* Test inputs and outputs. *)

(* A test input is a basename, without the .lambda extension. *)

type input =
  | PositiveTest of filename

type inputs = input list

let print_input = function
  | PositiveTest basename ->
      basename

type outcome =
  | OK
  | Fail of string (* message *)

let print_outcome = function
  | OK ->
      ""
  | Fail msg ->
      msg

type output =
  input * outcome

type outputs = output list

let print_output (input, outcome) =
  printf "\n[FAIL] %s\n%s"
    (print_input input)
    (print_outcome outcome)

(* -------------------------------------------------------------------------- *)

(* Auxiliary functions. *)

let check_expected directory id result expected =
  let cmd = sep ["cd"; directory; "&&"; "cp"; "-f"; result; expected] in
  let copy() =
    if command cmd <> 0 then
      fail id "Failed to create %s.\n" expected
  in
  (* If we are supposed to create the [expected] file, do so. *)
  if create_expected then
    copy()
  (* Otherwise, check that the file [expected] exists. If it does not exist,
     create it by renaming [result] to [expected], then fail and invite the
     user to review the newly created file. *)
  else if not (file_exists (directory ^ "/" ^ expected)) then begin
    copy();
    let cmd = sep ["more"; directory ^ "/" ^ expected] in
    fail id "The file %s did not exist.\n\
             I have just created it. Please review it.\n  %s\n"
      expected cmd
  end

(* -------------------------------------------------------------------------- *)

(* Running a positive test. *)

(*
  Conventions:
  The file %.c       stores the output of joujou.
  The file %.exe     is the compiled program produced by gcc.
  The file %.out     stores the output of the compiled program.
  The file %.exp     stores the expected output.
  The file %.err     stores error output (at several stages).
 *)

let process_positive_test (base : string) : unit =

  (* Display an information message. *)
  log 2 "Testing %s...\n%!" base;

  (* A suggested command. *)
  let more filename =
    sep ["more"; good_slash filename]
  in

  (* Run joujou. *)
  let source = lambda base in
  let c = base ^ ".c" in
  let errors = base ^ ".err" in
  let cmd = sep (
    "cd" :: good :: "&&" ::
    joujou :: source :: sprintf ">%s" c :: sprintf "2>%s" errors :: []
  ) in
  if command cmd <> 0 then
    fail base "joujou fails on this source file.\n\
               To see the source file:\n  %s\n\
               To see the error messages:\n  %s\n"
               (more source) (more errors);

  (* Run the C compiler. *)
  let binary = base ^ ".exe" in
  let errors = base ^ ".err" in
  let cmd = sep (
    "cd" :: good :: "&&" ::
    gcc :: c :: "-o" :: binary :: sprintf "2>%s" errors :: []
  ) in
  if command cmd <> 0 then
    fail base "The C compiler rejects the C file.\n\
               To see the C file:\n  %s\n\
               To see the compiler's error messages:\n  %s\n"
               (more c) (more errors);

  (* Run the compiled program. *)
  let out = base ^ ".out" in
  let cmd = sep (
    "cd" :: good :: "&&" ::
    sprintf "./%s" binary :: sprintf ">%s" out :: "2>&1" :: []
  ) in
  if command cmd <> 0 then
    fail base "The compiled program fails.\n\
               To see its output:\n  %s\n" (more out);

  (* Check that the file [exp] exists. *)
  let exp = base ^ ".exp" in
  check_expected good base out exp;

  (* Check that the output coincides with what was expected. *)
  let cmd = sep ("cd" :: good :: "&&" :: "diff" :: exp :: out :: []) in
  if command (silent cmd) <> 0 then
    fail base "joujou accepts this input file, but produces incorrect output.\n\
               To see the difference:\n  (%s)\n"
      cmd;

  (* Succeed. *)
  log 1 "[OK] %s\n%!" base

(* -------------------------------------------------------------------------- *)

(* Running a test. *)

let process input : output =
  try
    begin match input with
    | PositiveTest basenames ->
        process_positive_test basenames
    end;
    input, OK
  with Failure msg ->
    input, Fail msg

(* -------------------------------------------------------------------------- *)

(* [run] runs a bunch of tests in sequence. *)

let run (inputs : inputs) : outputs =
  flush stdout; flush stderr;
  let outputs = map process inputs in
  outputs

(* -------------------------------------------------------------------------- *)

(* Main. *)

(* Menhir can accept several .mly files at once. By convention, if several
   files have the same name up to a numeric suffix, then they belong in a
   single group and should be fed together to Menhir. *)

let inputs directory : filename list =
     readdir directory
  |> to_list
  |> filter (has_suffix ".lambda")
  |> map chop_extension
  |> sort compare

let positive : inputs =
     inputs good
  |> map (fun basename -> PositiveTest basename)

let inputs =
  positive

let outputs : outputs =
  printf "Preparing to run %d tests...\n%!" (length inputs);
  run inputs

let successful, failed =
  partition (fun (_, o) -> o = OK) outputs

let () =
  printf "%d out of %d tests are successful.\n"
    (length successful) (length inputs);
  failed |> iter (fun (input, outcome) ->
    printf "\n[FAIL] %s\n%s" (print_input input) (print_outcome outcome)
  )
