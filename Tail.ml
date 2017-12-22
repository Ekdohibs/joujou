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
     with actual arguments [vs]. (The value [v] should be a function, and its
     arity should be the length of [vs].)

   - The continuation call [ContCall (v, k, vs)] transfers control to the
     function [v], with actual arguments [vs], and continuation to apply [k].
     (The values [v] and [k] should be functions, [k] having arity exactly 1.)

   - The term [Print (v, t)] prints the value [v], then executes the term [t].
     (The value [v] should be a primitive integer value.)

   - The term [LetVal (x, v, t)] binds the variable [x] to the value [v], then
     executes the term [t].

   - The term [LetBlo (x, b, t)] allocates the memory block [b] and binds the
     variable [x] to its address, then executes the term [t].


   The semantics of [ContCall (f, k, [x1; ...; xn])] are defined as follows:

   - [ContCall (f, k, [x1; ...; xn]) -> TailCall (f, [x1; ...; xn; k])] if
     f has arity n + 1.

   - [ContCall (f, k, [x1; ...; xn]) ->
       TailCall (k, (fun x_{n+1} ... xm k2 -> ContCall (f, k2, [x1; ...; xm])))]
     if f has arity m + 1 > n + 1.

   - [ContCall (f, k, [x1; ...; xn]) ->
       TailCall (f, [x1; ...; xm; (fun g -> ContCall (g, k, [x_{m+1}; ...; xn]))])]
     if f has arity m + 1 < n + 1.
*)

and term =
  | Exit
  | TailCall of value * value list
  | ContCall of value * value * value list
  | Print of value * term
  | LetVal of variable * value * term
  | LetBlo of variable * block * term
  | IfZero of value * term * term

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
  | ContCall (v, k, vs) ->
    fv_values (v :: k :: vs)
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
  | IfZero (v1, t2, t3) ->
    union (fv_value v1) (union (fv_term t2) (fv_term t3))

let rec rename_value (r : Atom.atom Atom.Map.t) (v : value) =
  match v with
  | VVar x ->
    VVar (try Atom.Map.find x r
          with Not_found -> x)
  | VLit _ -> v
  | VBinOp (v1, op, v2) -> VBinOp (rename_value r v1, op, rename_value r v2)

and rename_values (r : Atom.atom Atom.Map.t) (vs : value list) =
  List.map (rename_value r) vs

and rename_lambda (r : Atom.atom Atom.Map.t) (xs : variable list) (t : term) =
  assert (not (List.exists (fun v -> Atom.Map.mem v r) xs));
  rename_term r t

and rename_block (r : Atom.atom Atom.Map.t) (b : block) =
  match b with
  | Lam (NoSelf, xs, t) ->
      Lam (NoSelf, xs, rename_lambda r xs t)
  | Lam (Self f, xs, t) ->
      Lam (Self f, xs, rename_lambda r (f :: xs) t)

and rename_term (r : Atom.atom Atom.Map.t) (t : term) =
  match t with
  | Exit -> Exit
  | TailCall (v, vs) ->
    TailCall (rename_value r v, rename_values r vs)
  | ContCall (v, k, vs) ->
    ContCall (rename_value r v, rename_value r k, rename_values r vs)
  | Print (v1, t2) ->
    Print (rename_value r v1, rename_term r t2)
  | LetVal (x, v1, t2) ->
    assert (not (Atom.Map.mem x r));
    LetVal (x, rename_value r v1, rename_term r t2)
  | LetBlo (x, b1, t2) ->
    assert (not (Atom.Map.mem x r));
    LetBlo (x, rename_block r b1, rename_term r t2)
  | IfZero (v1, t2, t3) ->
    IfZero (rename_value r v1, rename_term r t2, rename_term r t3)


(* [let x_1 = v_1 in ... let x_n = v_n in t] *)

let rec sequential_let (xs : variable list) (vs : value list) (t : term) =
  match xs, vs with
  | [], [] ->
      t
  | x :: xs, VVar v :: vs ->
      rename_term (Atom.Map.singleton x v) (sequential_let xs vs t)
  | x :: xs, v :: vs ->
      LetVal (x, v, sequential_let xs vs t)
  | _ ->
      assert false

(* [let x_1 = v_1 and ... x_n = v_n in t] *)

let parallel_let (xs : variable list) (vs : value list) (t : term) =
  assert (List.length xs = List.length vs);
  assert (Atom.Set.disjoint (Atom.Set.of_list xs) (fv_values vs));
  sequential_let xs vs t

let rec simpl (t : term) : term =
  match t with
  | Exit | TailCall _ | ContCall _ | Print _ -> t
  | LetVal (x, VVar v, t) ->
    rename_term (Atom.Map.singleton x v) (simpl t)
  | LetVal (x, v, t) -> LetVal (x, v, simpl t)
  | LetBlo (f, Lam (self, args, body), t) ->
    let t = simpl t in
    let body = simpl body in
    begin match t with
      | TailCall (VVar f1, vals) when Atom.equal f f1 && self = NoSelf ->
        parallel_let args vals body
      | _ -> LetBlo (f, Lam (self, args, body), t)
    end
  | IfZero (v, t1, t2) -> IfZero (v, simpl t1, simpl t2)

let optimize = simpl
