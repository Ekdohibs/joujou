open Error

(* The source calculus. *)
module S = RawLambda
(* The target calculus. *)
module T = Lambda
module TV = T.TV
module Ty = T.Ty
module TVSet = T.TVSet

let disable_type_checking = ref false

exception UnificationFailure of Ty.t * Ty.t

let unification_error t1 t2 =
  raise (UnificationFailure (Ty.canon t1, Ty.canon t2))

let rec occur var t =
  let open T in
  match (Ty.head t) with
  | Tint -> false
  | Tarrow (ta, tb) -> occur var ta || occur var tb
  | Tproduct l -> List.exists (occur var) l
  | Tvar tv -> TV.equal tv var

let rec unify t1 t2 =
  let open T in
  match (Ty.head t1), (Ty.head t2) with
  | Tint, Tint -> ()
  | Tarrow (t1a, t1b), Tarrow (t2a, t2b) -> unify t1a t2a; unify t1b t2b
  | Tproduct l1, Tproduct l2 ->
    if List.length l1 <> List.length l2 then
      unification_error t1 t2
    else
      List.iter2 unify l1 l2
  | Tvar tv1, Tvar tv2 ->
    if not (TV.equal tv1 tv2) then tv1.def <- Some t2
  | Tvar tv, t | t, Tvar tv ->
    if occur tv t then
      unification_error t1 t2
    else
      tv.def <- Some t
  | _ -> unification_error t1 t2

let check_unify place t1 t2 =
  if not !disable_type_checking then
    try unify t1 t2 with
    | UnificationFailure (ty1, ty2) ->
      error place "This expression has type %s but was expected of type %s." (T.show_typ (Ty.canon t1)) (T.show_typ (Ty.canon t2))

type schema = { vars : TVSet.t ; typ : Ty.t }

module Smap = Map.Make(String)
type env = {
  bindings : (schema * Atom.atom) Smap.t ;
  fvars : TVSet.t
}

let recompute_fvars fv =
  (* If the definitions of some variables changed, then the free variables
     might not be the same. However, the new set of free variables is exactly
     the set of free variables obtained from current definition of the
     previous free variables.
  *)
  TVSet.fold (fun v f -> TVSet.union f (Ty.fvars (T.Tvar v))) fv TVSet.empty

let update_fvars env =
  { env with fvars = recompute_fvars env.fvars }

let empty_env = { bindings = Smap.empty ; fvars = TVSet.empty }

let add id typ env =
  let fv = Ty.fvars typ in
  let a = Atom.fresh id in
  let nenv = {
    bindings = Smap.add id
        ({ vars = TVSet.empty ; typ = typ }, a)
        env.bindings ;
    fvars = TVSet.union (recompute_fvars env.fvars) fv ;
  } in
  (nenv, a)

let add_gen id typ env =
  let fv = Ty.fvars typ in
  let a = Atom.fresh id in
  let nenv = {
    bindings = Smap.add id
        ({ vars = TVSet.diff fv (recompute_fvars env.fvars); typ = typ }, a)
        env.bindings ;
    fvars = recompute_fvars env.fvars ;
  } in
  (nenv, a)

let print_env ff env =
  Format.fprintf ff "-----@.";
  Smap.iter (fun x ({vars ; typ}, _) ->
      Format.fprintf ff "%s : forall " x;
      TVSet.iter (fun v -> Format.fprintf ff "%s " (T.show_tvar v)) vars;
      Format.fprintf ff ". %s@." (T.show_typ (Ty.canon typ))
    ) env;
  Format.fprintf ff "-----@."

let refresh vars t =
  let module VarMap = Map.Make(TV) in
  let m = TVSet.fold
      (fun v m -> VarMap.add v (TV.create ()) m) vars VarMap.empty in
  Ty.subst (fun v -> T.Tvar (try VarMap.find v m with Not_found -> v)) t

let find id env =
  let ({ vars = vars; typ = typ }, a) = Smap.find id env.bindings in
  refresh vars typ, a

let rec cook_term env { S.place; S.value } =
  match value with
  | S.Var x -> begin
    match find x env with
    | typ, a -> typ, T.Var a
    | exception Not_found -> error place "Unbound variable: %s" x
    end
  | S.Lam (x, t) ->
    let tv = T.Tvar (TV.create ()) in
    let env, x = add x tv env in
    let typ, t = cook_term env t in
    T.Tarrow (tv, typ), T.Lam (T.NoSelf, x, t)
  | S.App (t1, t2) ->
    let ty1, nt1 = cook_term env t1 in
    let ty2, nt2 = cook_term env t2 in
    let tv = T.Tvar (TV.create ()) in
    check_unify t1.S.place ty1 (T.Tarrow (ty2, tv));
    tv, T.App (nt1, nt2)
  | S.Lit i ->
    T.Tint, T.Lit i
  | S.BinOp (t1, op, t2) ->
    let ty1, nt1 = cook_term env t1 in
    let ty2, nt2 = cook_term env t2 in
    check_unify t1.S.place ty1 T.Tint;
    check_unify t2.S.place ty2 T.Tint;
    T.Tint, T.BinOp (nt1, op, nt2)
  | S.Print t ->
    let ty, nt = cook_term env t in
    check_unify t.S.place ty T.Tint;
    T.Tint, T.Print nt
  | S.CallCc t ->
    let ty, t = cook_term env t in
    let tv = T.Tvar (TV.create ()) in
    if not !disable_type_checking then
      error place "Please disable type-checking if you want to use callcc";
    tv, T.CallCc t
  | S.Let (S.NonRecursive, x, t1, t2) ->
    let ty1, t1 = cook_term env t1 in
    let env, x = add_gen x ty1 env in
    let ty2, t2 = cook_term env t2 in
    ty2, T.Let (x, t1, t2)
  | S.Let (S.Recursive, f, { S.value = S.Lam (x, t1); _ }, t2) ->
    let tv = T.Tvar (TV.create ()) in
    let ty1, x, f1, nt1 =
      let env, f = add f tv env in
      let tv1 = T.Tvar (TV.create ()) in
      let env, x = add x tv1 env in
      let ty1, nt1 = cook_term env t1 in
      T.Tarrow (tv1, ty1), x, f, nt1
    in
    check_unify t1.S.place tv ty1;
    let env, f2 = add_gen f ty1 env in
    let ty2, nt2 = cook_term env t2 in
    ty2, T.Let (f2, T.Lam (T.Self f1, x, nt1), nt2)
  | S.Let (S.Recursive, _, { S.place; _ }, _) ->
    error place "the right-hand side of 'let rec' must be a lambda-abstraction"
  | S.IfZero (t1, t2, t3) ->
    let ty1, nt1 = cook_term env t1 in
    let ty2, nt2 = cook_term env t2 in
    let ty3, nt3 = cook_term env t3 in
    check_unify t1.S.place ty1 T.Tint;
    check_unify t3.S.place ty2 ty3;
    ty2, T.IfZero (nt1, nt2, nt3)
  | S.Match _ -> assert false



let cook_term t =
  snd (cook_term empty_env t)

let cook_program = function
  | [{S.value = S.DTerm t; _}] -> cook_term t
  | _ -> assert false
