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

type 'a tvar = {
  id : int ;
  mutable def : 'a option ;
}

[@@deriving show { with_path = false }]

type variable =
  Atom.atom

and tname =
  Atom.atom

and constructor =
  Atom.atom * int * bool

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
  | Tuple of term list
  | Constructor of constructor * term list
  | Match of term * (pattern_or_effect * term) list

and pattern =
  | PVar of variable
  | PConstructor of constructor * pattern list
  | POr of pattern * pattern
  | PTuple of pattern list

and pattern_or_effect =
  | Pattern of pattern
  | Effect of pattern * variable

and typ =
  | Tident of tname
  | Tarrow of typ * row * typ
  | Tproduct of typ list
  | Tvar of typ tvar

and row =
  | Reffect of tname * row
  | Rvar of row tvar
  | Rempty

[@@deriving show { with_path = false }]

module TV_ = struct
  type t =
    | TVty of typ tvar
    | TVrow of row tvar
  let of_typevar tv = TVty tv
  let to_typevar = function
    | TVty tv -> tv
    | _ -> assert false
  let of_rowvar tv = TVrow tv
  let to_rowvar = function
    | TVrow tv -> tv
    | _ -> assert false
  let get_id = function
    | TVty v -> v.id
    | TVrow v -> v.id
  let compare v1 v2 = compare (get_id v1) (get_id v2)
  let equal v1 v2 = (get_id v1) = (get_id v2)
  let eq v1 v2 = v1.id = v2.id
  let r = ref 0
  let create () = incr r ; { id = !r ; def = None }
  let copy = function
    | TVty _ -> TVty (create ())
    | TVrow _ -> TVrow (create ())
end

module TVSet = Set.Make(TV_)
module TVMap = Map.Make(TV_)

module Row = struct
  type t = row

  let rec head r =
    match r with
    | Rvar {def = Some r' ; _} -> head r'
    | _ -> r

  let rec canon r =
    match r with
    | Reffect (name, r) -> Reffect (name, canon r)
    | Rempty -> Rempty
    | Rvar {def = None ; _} -> r
    | Rvar {def = Some r ; _} -> canon r

  let rec fvars r =
    match head r with
    | Reffect (_, r) -> fvars r
    | Rempty -> TVSet.empty
    | Rvar rv -> TVSet.singleton (TV_.of_rowvar rv)

  let rec refresh_rec sigma r =
    match head r with
    | Rempty -> Rempty
    | Reffect (name, r) -> Reffect (name, refresh_rec sigma r)
    | Rvar tv ->
      try Rvar (TV_.to_rowvar (TVMap.find (TV_.of_rowvar tv) sigma))
      with Not_found -> Rvar tv

  let rec print sigma ff r =
    match (head r) with
    | Rempty -> ()
    | Reffect (name, r) ->
      Format.fprintf ff "%s |@ %a" (Atom.hint name) (print sigma) r
    | Rvar tv -> Format.fprintf ff "%s" (TVMap.find (TV_.of_rowvar tv) sigma)
end

module Ty = struct
  type t = typ

  let rec head t =
    match t with
    | Tvar {def = Some t' ; _} -> head t'
    | _ -> t

  let rec canon t =
    match t with
    | Tident _ -> t
    | Tarrow (ta, r, tb) -> Tarrow (canon ta, Row.canon r, canon tb)
    | Tproduct l -> Tproduct (List.map canon l)
    | Tvar {def = None ; _} -> t
    | Tvar {def = Some ty ; _} -> canon ty

  let rec fvars t =
    match head t with
    | Tident _ -> TVSet.empty
    | Tarrow (ta, r, tb) ->
      TVSet.union (fvars ta) (TVSet.union (Row.fvars r) (fvars tb))
    | Tproduct l ->
      List.fold_left TVSet.union TVSet.empty (List.map fvars l)
    | Tvar tv -> TVSet.singleton (TV_.of_typevar tv)

  let rec refresh_rec sigma t =
    match head t with
    | Tident n -> Tident n
    | Tarrow (t1, r, t2) ->
      Tarrow (refresh_rec sigma t1, Row.refresh_rec sigma r,
              refresh_rec sigma t2)
    | Tproduct l -> Tproduct (List.map (refresh_rec sigma) l)
    | Tvar tv ->
      try Tvar (TV_.to_typevar (TVMap.find (TV_.of_typevar tv) sigma))
      with Not_found -> Tvar tv

  let refresh vars t =
    let m = TVSet.fold
        (fun v m -> TVMap.add v (TV_.copy v) m) vars TVMap.empty in
    refresh_rec m t
(*
  let rec subst sigma t =
    match (head t) with
    | Tident n -> Tident n
    | Tarrow (t1, r, t2) ->
      Tarrow (subst sigma t1, r, subst sigma t2)
    | Tproduct l -> Tproduct (List.map (subst sigma) l)
    | Tvar tv -> sigma tv
*)
  let rec print sigma level ff t =
    match (head t) with
    | Tident n -> Format.fprintf ff "%s" (Atom.hint n)
    | Tarrow (t1, r, t2) ->
      if level >= 3 then Format.fprintf ff "(";
      Format.fprintf ff "%a -[@[<hov 2>%a@]]->@ @[<hv>%a@]"
        (print sigma 3) t1 (Row.print sigma) r (print sigma 2) t2;
      if level >= 3 then Format.fprintf ff ")"
    | Tproduct l ->
      if level >= 4 then Format.fprintf ff "(";
      List.iteri (fun i t ->
          if i > 0 then Format.fprintf ff " *@ ";
          Format.fprintf ff "%a" (print sigma 4) t
      ) l;
      if level >= 4 then Format.fprintf ff ")"
    | Tvar tv -> Format.fprintf ff "%s" (TVMap.find (TV_.of_typevar tv) sigma)
end

module TV : sig
  type t = TV_.t
  val compare : t -> t -> int
  val eq : 'a tvar -> 'a tvar -> bool
  val equal : t -> t -> bool
  val of_typevar : typ tvar -> t
  val to_typevar : t -> typ tvar
  val of_rowvar : row tvar -> t
  val to_rowvar : t -> row tvar
  val create : unit -> 'a tvar
  val copy : t -> t
  val recompute_fvars : TVSet.t -> TVSet.t
  val get_print_names : TVSet.t -> TVSet.t -> string TVMap.t
end = struct
  include TV_
  let recompute_fvar = function
    | TVty tv -> Ty.fvars (Tvar tv)
    | TVrow tv -> Row.fvars (Rvar tv)
  let recompute_fvars fv =
    TVSet.fold (fun v f -> TVSet.union f (recompute_fvar v)) fv TVSet.empty
  let get_print_names vars generalized =
    let sigma, _ = TVSet.fold (fun v (m, i) ->
      let s = String.make 1 (char_of_int ((i mod 26) + 97)) in
      let s = if i > 26 then s ^ string_of_int (i / 26) else s in
      let s = if TVSet.mem v generalized then s else "_" ^ s in
      let s = (match v with TVty _ -> "'" | TVrow _ -> "!") ^ s in
      (TVMap.add v s m, i + 1)
    ) vars (TVMap.empty, 0) in
    sigma
end
