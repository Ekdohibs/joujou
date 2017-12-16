(* This language is the untyped lambda-calculus, extended with recursive
   lambda-abstractions, nonrecursive [let] bindings, integer literals and
   integer arithmetic operations, and the primitive operation [print]. *)

(* This language is really the same language as [RawLambda], with the
   following internal differences:

   1. Instead of recursive [let] bindings, the language has recursive
      lambda-abstractions. A [let rec] definition whose right-hand side is not
      a lambda-abstraction is rejected during the translation of [RawLambda]
      to [Lambda].

   2. Variables are represented by atoms (instead of strings). A term with an
      unbound variable is rejected during the translation of [RawLambda] to
      [Lambda].

   3. Terms are no longer annotated with places. *)

(* Variables are atoms. *)

type variable =
  Atom.atom

 (* Every lambda-abstraction is marked recursive or nonrecursive. Whereas a
   nonrecursive lambda-abstraction [fun x -> t] binds one variable [x], a
   recursive lambda-abstraction [fix f. fun x -> t] binds two variables [f]
   and [x]. The variable [f] is a self-reference. *)

and self =
  | Self of variable
  | NoSelf

and binop = RawLambda.binop =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv

and term =
  | Var of variable
  | Lam of self * variable * term
  | App of term * term
  | Lit of int
  | BinOp of term * binop * term
  | Print of term
  | Let of variable * term * term

[@@deriving show { with_path = false }]
