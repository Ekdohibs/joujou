type filename = string
type command = string

let has_suffix suffix name =
  Filename.check_suffix name suffix

let fail format =
  Printf.kprintf failwith format

let try_finally f h =
  let result = try f() with e -> h(); raise e in
  h(); result

let with_process_code_result command (f : in_channel -> 'a) : int * 'a =
  let ic = Unix.open_process_in command in
  set_binary_mode_in ic false;
  match f ic with
  | exception e ->
      ignore (Unix.close_process_in ic); raise e
  | result ->
      match Unix.close_process_in ic with
      | Unix.WEXITED code ->
          code, result
      | Unix.WSIGNALED _
      | Unix.WSTOPPED _ ->
          99 (* arbitrary *), result

let with_process_result command (f : in_channel -> 'a) : 'a =
  let code, result = with_process_code_result command f in
  if code = 0 then
    result
  else
    fail "Command %S failed with exit code %d." command code

let with_open_in filename (f : in_channel -> 'a) : 'a =
  let ic = open_in filename in
  try_finally
    (fun () -> f ic)
    (fun () -> close_in_noerr ic)

let with_open_out filename (f : out_channel -> 'a) : 'a =
  let oc = open_out filename in
  try_finally
    (fun () -> f oc)
    (fun () -> close_out_noerr oc)

let chunk_size =
  16384

let exhaust (ic : in_channel) : string =
  let buffer = Buffer.create chunk_size in
  let chunk = Bytes.create chunk_size in
  let rec loop () =
    let length = input ic chunk 0 chunk_size in
    if length = 0 then
      Buffer.contents buffer
    else begin
      Buffer.add_subbytes buffer chunk 0 length;
      loop()
    end
  in
  loop()

let read_whole_file filename =
  with_open_in filename exhaust

let absolute_directory (path : string) : string =
  try
    let pwd = Sys.getcwd() in
    Sys.chdir path;
    let result = Sys.getcwd() in
    Sys.chdir pwd;
    result
  with Sys_error _ ->
    Printf.fprintf stderr "Error: the directory %s does not seem to exist.\n" path;
    exit 1

let get_number_of_cores () =
  try match Sys.os_type with
  | "Win32" ->
      int_of_string (Sys.getenv "NUMBER_OF_PROCESSORS")
  | _ ->
      with_process_result "getconf _NPROCESSORS_ONLN" (fun ic ->
        let ib = Scanf.Scanning.from_channel ic in
        Scanf.bscanf ib "%d" (fun n -> n)
      )
  with
  | Not_found
  | Sys_error _
  | Failure _
  | Scanf.Scan_failure _
  | End_of_file
  | Unix.Unix_error _ ->
      1

let silent command : command =
  command ^ " >/dev/null 2>/dev/null"

(* [groups eq xs] segments the list [xs] into a list of groups, where several
   consecutive elements belong in the same group if they are equivalent in the
   sense of the function [eq]. *)

(* The auxiliary function [groups1] deals with the case where we have an open
   group [group] of which [x] is a member. The auxiliary function [group0]
   deals with the case where we have no open group. [groups] is the list of
   closed groups found so far, and [ys] is the list of elements that remain to
   be examined. *)

let rec groups1 eq groups x group ys =
  match ys with
  | [] ->
      group :: groups
  | y :: ys ->
      if eq x y then
        groups1 eq groups x (y :: group) ys
      else
        groups0 eq (List.rev group :: groups) (y :: ys)

and groups0 eq groups ys =
  match ys with
  | [] ->
      groups
  | y :: ys ->
      groups1 eq groups y [y] ys

let groups eq (xs : 'a list) : 'a list list =
  List.rev (groups0 eq [] xs)

(* [sep ss] separates the nonempty strings in the list [ss] with a space,
   and concatenates everything, producing a single string. *)

let sep (ss : string list) : string =
  let ss = List.filter (fun s -> String.length s > 0) ss in
  match ss with
  | [] ->
      ""
  | s :: ss ->
      List.fold_left (fun s1 s2 -> s1 ^ " " ^ s2) s ss
