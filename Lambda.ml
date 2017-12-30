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
      [Lambda]. The same is done for types and constructors.

   3. Terms are no longer annotated with places. *)

(* Variables are atoms. *)

type variable =
  Atom.atom

and tname =
  Atom.atom

and constructor =
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
  | IfZero of term * term * term
  | CallCc of term
  | Tuple of term list
  | Constructor of constructor * term list

and typ =
  | Tident of tname
  | Tarrow of typ * typ
  | Tproduct of typ list
  | Tvar of tvar

and tvar = {
  id : int ;
  mutable def : typ option ;
}

[@@deriving show { with_path = false }]

module TV = struct
  type t = tvar
  let compare v1 v2 = compare v1.id v2.id
  let equal v1 v2 = v1.id = v2.id
  let create = let r = ref 0 in fun () -> incr r; { id = !r ; def = None }
end

module TVSet = Set.Make(TV)

module Ty = struct
  type t = typ

  let rec head t =
    match t with
    | Tvar {def = Some t'; _} -> head t'
    | _ -> t

  let rec canon t =
    match t with
    | Tident _ -> t
    | Tarrow (ta, tb) -> Tarrow (canon ta, canon tb)
    | Tproduct l -> Tproduct (List.map canon l)
    | Tvar {def = None ; _} -> t
    | Tvar {def = Some ty ; _} -> canon ty

  let rec fvars t =
    match (head t) with
    | Tident _ -> TVSet.empty
    | Tarrow (ta, tb) -> TVSet.union (fvars ta) (fvars tb)
    | Tproduct l ->
      List.fold_left TVSet.union TVSet.empty (List.map fvars l)
    | Tvar tv -> TVSet.singleton tv

  let rec subst sigma t =
    match (head t) with
    | Tident n -> Tident n
    | Tarrow (t1, t2) -> Tarrow (subst sigma t1, subst sigma t2)
    | Tproduct l -> Tproduct (List.map (subst sigma) l)
    | Tvar tv -> sigma tv
end
