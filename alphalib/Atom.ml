(* -------------------------------------------------------------------------- *)

(* We impose maximal sharing on strings so as to reduce the total amount of
   space that they occupy. This is done using a weak hash set. *)

module StringStorage =
  Weak.Make(struct
    type t = string
    let equal (s1 : string) (s2 : string) = (s1 = s2)
    let hash = Hashtbl.hash
  end)

let share : string -> string =
  StringStorage.merge (StringStorage.create 128)

(* -------------------------------------------------------------------------- *)

(* Removing any trailing digits in a string. *)

let is_digit c =
  Char.code '0' <= Char.code c && Char.code c <= Char.code '9'

let remove_trailing_digits (s : string) : string =
  let n = ref (String.length s) in
  while !n > 0 && is_digit s.[!n-1] do n := !n-1 done;
  (* We assume that there is at least one non-digit character in the string. *)
  assert (!n > 0);
  String.sub s 0 !n

(* -------------------------------------------------------------------------- *)

(* An atom is implemented as a pair of an integer identity and a string that
   serves as a printing hint. *)

(* We maintain the invariant that a hint is nonempty and does not end in a
   digit. This allows us to later produce unique identifiers, without risk of
   collisions, by concatenating a hint and a unique number. *)

(* To preserve space, hints are maximally shared. This is not essential for
   correctness, though. *)

type atom = { identity: int; hint: string }

and t = atom
  [@@deriving show { with_path = false }]

let identity a =
  a.identity

let hint a =
  a.hint

(* -------------------------------------------------------------------------- *)

(* A global integer counter holds the next available identity. *)

let counter =
  ref 0

let allocate () =
  let number = !counter in
  counter := number + 1;
  assert (number >= 0);
  number

(* [fresh hint] produces a fresh atom. *)

(* The argument [hint] must not be a string of digits. *)

let fresh hint =
  let identity = allocate()
  and hint = share (remove_trailing_digits hint) in
  { identity; hint }

(* [copy a] returns a fresh atom modeled after the atom [a]. *)

let copy a =
  fresh a.hint

(* -------------------------------------------------------------------------- *)

(* Comparison of atoms. *)

let equal a b =
  a.identity = b.identity

let compare a b =
  (* Identities are always positive numbers (see [allocate] above)
     so I believe overflow is impossible here. *)
  a.identity - b.identity

let hash a =
  Hashtbl.hash a.identity

(* -------------------------------------------------------------------------- *)

(* A scratch buffer for printing. *)

let scratch =
  Buffer.create 1024

(* [print_separated_sequence] prints a sequence of elements into the [scratch]
   buffer. The sequence is given by the higher-order iterator [iter], applied
   to the collection [xs]. The separator is the string [sep]. Each element is
   transformed to a string by the function [show]. *)

let print_separated_sequence show sep iter xs : unit =
  let first = ref true in
  iter (fun x ->
    if !first then begin
      Buffer.add_string scratch (show x);
      first := false
    end
    else begin
      Buffer.add_string scratch sep;
      Buffer.add_string scratch (show x)
    end
  ) xs

(* -------------------------------------------------------------------------- *)

(* Sets and maps. *)

module Order = struct
  type t = atom
  let compare = compare
end

module Set = struct

  include Set.Make(Order)

  (* A disjointness test. *)

  let disjoint xs ys =
    is_empty (inter xs ys)

  (* Iterated union. *)

  let union_many (f : 'a -> t) (xs : 'a list) : t =
    List.fold_left (fun accu x ->
      union accu (f x)
      ) empty xs

  (* Disjoint union. *)

  exception NonDisjointUnion of atom

  let disjoint_union xs ys =
    match choose (inter xs ys) with
    | exception Not_found ->
        (* The intersection of [xs] and [ys] is empty. Return their union. *)
        union xs ys
    | x ->
        (* The intersection contains [x]. Raise an exception. *)
        raise (NonDisjointUnion x)

  let handle_NonDisjointUnion f x =
    try
      f x; true
    with NonDisjointUnion a ->
      Printf.eprintf "NonDisjointUnion: %s\n%!" (show a);
      false

  (* Sets of atoms form a monoid under union. *)

  class ['z] union_monoid = object
    method zero: 'z = empty
    method plus: 'z -> 'z -> 'z = union
  end

  (* Sets of atoms form a monoid under disjoint union. *)

  class ['z] disjoint_union_monoid = object
    method zero: 'z = empty
    method plus: 'z -> 'z -> 'z = disjoint_union
  end

  (* These printing functions should be used for debugging purposes only. *)

  let print_to_scratch xs =
    Buffer.clear scratch;
    Buffer.add_string scratch "{";
    print_separated_sequence show ", " iter xs;
    Buffer.add_string scratch "}"

  let show xs =
    print_to_scratch xs;
    let result = Buffer.contents scratch in
    Buffer.reset scratch;
    result

  let print oc xs =
    print_to_scratch xs;
    Buffer.output_buffer oc scratch;
    Buffer.reset scratch

end

module Map = struct

  include Map.Make(Order)

  (* This is O(nlog n), whereas in principle O(n) is possible.
     The abstraction barrier in OCaml's [Set] module hinders us. *)
  let domain m =
    fold (fun a _ accu -> Set.add a accu) m Set.empty

  let codomain f m =
    fold (fun _ v accu -> Set.union (f v) accu) m Set.empty

end

type renaming =
  atom Map.t
