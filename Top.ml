(* This intermediate language describes the result of defunctionalization.
   It retains the key features of the previous calculus, [Tail], in that
   the ordering of computations is explicit and every function call is a
   tail call. Furthermore, lambda-abstractions disappear. A memory block
   [Con] now contains an integer tag followed with a number of fields,
   which hold values. A [switch] construct appears, which allows testing
   the tag of a memory block. A number of (closed, mutually recursive)
   functions can be defined at the top level. *)

type tag =
  int

and variable =
  Atom.atom

and binop = Tail.binop =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv

and value = Tail.value =
  | VVar of variable
  | VLit of int
  | VBinOp of value * binop * value

(* A block contains an integer tag, followed with a number of fields. *)

and block =
  | Con of tag * value list

(* The construct [Swi (v, branches)] reads the integer tag stored in the
   memory block at address [v] and performs a case analysis on this tag,
   transferring control to the appropriate branch. (The value [v] should be a
   pointer to a memory block.) *)

and term =
  | Exit
  | TailCall of variable * value list
  | Print of value * term
  | LetVal of variable * value * term
  | LetBlo of variable * block * term
  | Swi of value * branch list

(* A branch [tag xs -> t] is labeled with an integer tag [tag], and is
   executed if the memory block carries this tag. The variables [xs] are
   then bounds to the fields of the memory block. (The length of the list
   [xs] should be the number of fields of the memory block.) *)

and branch =
  | Branch of tag * variable list * term

(* A toplevel function declaration mentions the function's name, formal
   parameters, and body. *)

and function_declaration =
  | Fun of variable * variable list * term

(* A complete program consits of a set of toplevel function declarations
   and a term (the "main program"). The functions are considered mutually
   recursive: every function may refer to every function. *)

and program =
  | Prog of function_declaration list * term

[@@deriving show { with_path = false }]

(* -------------------------------------------------------------------------- *)

(* Constructor functions. *)

let vvar =
  Tail.vvar

let vvars =
  Tail.vvars

(* [let x_1 = v_1 in ... let x_n = v_n in t] *)

let rec sequential_let (xs : variable list) (vs : value list) (t : term) =
  match xs, vs with
  | [], [] ->
      t
  | x :: xs, v :: vs ->
      LetVal (x, v, sequential_let xs vs t)
  | _ ->
      assert false

(* [let x_1 = v_1 and ... x_n = v_n in t] *)

let parallel_let (xs : variable list) (vs : value list) (t : term) =
  assert (List.length xs = List.length vs);
  assert (Atom.Set.disjoint (Atom.Set.of_list xs) (Tail.fv_values vs));
  sequential_let xs vs t
