(* This intermediate language describes the result of the CPS transformation.
   It is a lambda-calculus where the ordering of computations is explicit and
   where every function call is a tail call.

   The following syntactic categories are distinguished:

   1. "Values" include variables, integer literals, and applications of the
      primitive integer operations to values. Instead of "values", they could
      also be referred to as "pure expressions". They are expressions whose
      evaluation terminates and has no side effect, not even memory
      allocation.

   2. "Blocks" include lambda-abstractions. Even though lambda-abstractions
      are traditionally considered values, here, they are viewed as
      expressions whose evaluation has a side effect, namely, the allocation
      of a memory block.

   3. "Terms" are expressions with side effects. Terms always appear in tail
      position: an examination of the syntax of terms shows that a term can be
      viewed as a sequence of [LetVal], [LetBlo] and [Print] instructions,
      terminated with either [Exit] or [TailCall]. This implies, in
      particular, that every call is a tail call.

   In contrast with the surface language, where every lambda-abstraction has
   arity 1, in this calculus, lambda-abstractions of arbitrary arity are
   supported. A lambda-abstraction [Lam] carries a list of formal arguments
   and a function call [TailCall] carries a list of actual arguments. Partial
   applications or over-applications are not supported: it is the programmer's
   responsibility to ensure that every function call provides exactly as many
   arguments as expected by the called function. *)

type variable =
  Atom.atom

and self = Lambda.self =
  | Self of variable
  | NoSelf

and binop = Lambda.binop =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv

and value =
  | VVar of variable
  | VLit of int
  | VBinOp of value * binop * value

and block =
  | Lam of self * variable list * term

(* Terms include the following constructs:

   - The primitive operation [Exit] stops the program.

   - The tail call [TailCall (v, vs)] transfers control to the function [v]
     with actual arguments [vs]. (The value [v] should be a function and its
     arity should be the length of [vs].)

   - The term [Print (v, t)] prints the value [v], then executes the term [t].
     (The value [v] should be a primitive integer value.)

   - The term [LetVal (x, v, t)] binds the variable [x] to the value [v], then
     executes the term [t].

   - The term [LetBlo (x, b, t)] allocates the memory block [b] and binds the
     variable [x] to its address, then executes the term [t]. *)

and term =
  | Exit
  | TailCall of value * value list
  | Print of value * term
  | LetVal of variable * value * term
  | LetBlo of variable * block * term

[@@deriving show { with_path = false }]

(* -------------------------------------------------------------------------- *)

(* Constructor functions. *)

let vvar x =
  VVar x

let vvars xs =
  List.map vvar xs

(* -------------------------------------------------------------------------- *)

(* Computing the free variables of a value, block, or term. *)

open Atom.Set

let rec fv_value (v : value) =
  match v with
  | VVar x ->
      singleton x
  | VLit _ ->
      empty
  | VBinOp (v1, _, v2) ->
      union (fv_value v1) (fv_value v2)

and fv_values (vs : value list) =
  union_many fv_value vs

and fv_lambda (xs : variable list) (t : term) =
  diff (fv_term t) (of_list xs)

and fv_block (b : block) =
  match b with
  | Lam (NoSelf, xs, t) ->
      fv_lambda xs t
  | Lam (Self f, xs, t) ->
      remove f (fv_lambda xs t)

and fv_term (t : term) =
  match t with
  | Exit ->
      empty
  | TailCall (v, vs) ->
      fv_values (v :: vs)
  | Print (v1, t2) ->
      union (fv_value v1) (fv_term t2)
  | LetVal (x, v1, t2) ->
      union
        (fv_value v1)
        (remove x (fv_term t2))
  | LetBlo (x, b1, t2) ->
      union
        (fv_block b1)
        (remove x (fv_term t2))
