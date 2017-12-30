open Error

(* The source calculus. *)
module S = RawLambda
(* The target calculus. *)
module T = Lambda
module TV = T.TV
module Ty = T.Ty
module TVSet = T.TVSet

let disable_type_checking = ref false

type schema = { vars : TVSet.t ; typ : Ty.t }

type typedef =
  | TBaseType of Atom.atom
  | TTypeSynonym of Ty.t

module Smap = Map.Make(String)
type env = {
  bindings : (schema * Atom.atom) Smap.t ;
  fvars : TVSet.t ;
  type_bindings : Atom.atom Smap.t ;
  type_defs : typedef Atom.Map.t ;
  constructor_bindings : Atom.atom Smap.t ;
  constructor_defs : (Atom.atom * Ty.t list) Atom.Map.t ;
}


let builtin_int_id = Atom.fresh "int"
let builtin_int = T.Tident builtin_int_id

let base_env = {
  bindings = Smap.empty ;
  fvars = TVSet.empty ;
  type_bindings = Smap.singleton "int" builtin_int_id ;
  type_defs = Atom.Map.singleton builtin_int_id (TBaseType builtin_int_id) ;
  constructor_bindings = Smap.empty ;
  constructor_defs = Atom.Map.empty ;
}

exception UnificationFailure of Ty.t * Ty.t

let unification_error t1 t2 =
  raise (UnificationFailure (Ty.canon t1, Ty.canon t2))

let rec occur var t =
  let open T in
  match (Ty.head t) with
  | Tident _ -> false
  | Tarrow (ta, tb) -> occur var ta || occur var tb
  | Tproduct l -> List.exists (occur var) l
  | Tvar tv -> TV.equal tv var

let rec resolve env t =
  let open T in
  match (Ty.head t) with
  | Tident n ->
    (match Atom.Map.find n env.type_defs with
     | TTypeSynonym t -> resolve env t
     | TBaseType n -> Tident n)
  | t -> t

let rec unify env t1 t2 =
  let open T in
  match (resolve env t1), (resolve env t2) with
  | Tident n1, Tident n2 ->
    if not (Atom.equal n1 n2) then
      unification_error t1 t2
  | Tarrow (t1a, t1b), Tarrow (t2a, t2b) ->
    unify env t1a t2a; unify env t1b t2b
  | Tproduct l1, Tproduct l2 ->
    if List.length l1 <> List.length l2 then
      unification_error t1 t2
    else
      List.iter2 (unify env) l1 l2
  | Tvar tv1, Tvar tv2 ->
    if not (TV.equal tv1 tv2) then tv1.def <- Some t2
  | Tvar tv, t | t, Tvar tv ->
    if occur tv t then
      unification_error t1 t2
    else
      tv.def <- Some t
  | _ -> unification_error t1 t2

let check_unify place env t1 t2 =
  if not !disable_type_checking then
    try unify env t1 t2 with
    | UnificationFailure (ty1, ty2) ->
      error place "This expression has type %s but was expected of type %s.@.The type %s is incompatible with the type %s" (T.show_typ (Ty.canon t1)) (T.show_typ (Ty.canon t2)) (T.show_typ (Ty.canon ty1)) (T.show_typ (Ty.canon ty2))

let recompute_fvars fv =
  (* If the definitions of some variables changed, then the free variables
     might not be the same. However, the new set of free variables is exactly
     the set of free variables obtained from current definition of the
     previous free variables.
  *)
  TVSet.fold (fun v f -> TVSet.union f (Ty.fvars (T.Tvar v))) fv TVSet.empty

let add id typ env =
  let fv = Ty.fvars typ in
  let a = Atom.fresh id in
  let nenv = { env with
    bindings = Smap.add id
        ({ vars = TVSet.empty ; typ = typ }, a)
        env.bindings ;
    fvars = TVSet.union (recompute_fvars env.fvars) fv ;
  } in
  (nenv, a)

let add_gen id typ env =
  let fv = Ty.fvars typ in
  let a = Atom.fresh id in
  let nenv = { env with
    bindings = Smap.add id
        ({ vars = TVSet.diff fv (recompute_fvars env.fvars) ; typ = typ }, a)
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
  let ({ vars = vars ; typ = typ }, a) = Smap.find id env.bindings in
  refresh vars typ, a

let rec cook_term env { S.place ; S.value } =
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
    check_unify t1.S.place env ty1 (T.Tarrow (ty2, tv));
    tv, T.App (nt1, nt2)
  | S.Lit i ->
    builtin_int, T.Lit i
  | S.BinOp (t1, op, t2) ->
    let ty1, nt1 = cook_term env t1 in
    let ty2, nt2 = cook_term env t2 in
    check_unify t1.S.place env ty1 builtin_int;
    check_unify t2.S.place env ty2 builtin_int;
    builtin_int, T.BinOp (nt1, op, nt2)
  | S.Print t ->
    let ty, nt = cook_term env t in
    check_unify t.S.place env ty builtin_int;
    builtin_int, T.Print nt
  | S.CallCc t ->
    let _, t = cook_term env t in
    let tv = T.Tvar (TV.create ()) in
    if not !disable_type_checking then
      error place "Please disable type-checking if you want to use callcc";
    tv, T.CallCc t
  | S.Let (recursive, x, t1, t2) ->
    let env, x, nt1 = cook_let env recursive x t1 in
    let ty2, nt2 = cook_term env t2 in
    ty2, T.Let (x, nt1, nt2)
  | S.IfZero (t1, t2, t3) ->
    let ty1, nt1 = cook_term env t1 in
    let ty2, nt2 = cook_term env t2 in
    let ty3, nt3 = cook_term env t3 in
    check_unify t1.S.place env ty1 builtin_int;
    check_unify t3.S.place env ty2 ty3;
    ty2, T.IfZero (nt1, nt2, nt3)
  | S.Match _ -> assert false
  | S.Tuple l ->
    let l = List.map (cook_term env) l in
    T.Tproduct (List.map fst l), (T.Tuple (List.map snd l))
  | S.Constructor (x, t) ->
    let catom =
      try Smap.find x env.constructor_bindings
      with Not_found -> error place "Unbound constructor: %s" x
    in
    let tname, cargs = Atom.Map.find catom env.constructor_defs in
    let n = List.length cargs in
    let args =
      match n, t with
      | 0, None -> []
      | 1, Some t -> [t]
      | 2, Some { S.value = (S.Tuple l) ; _ } -> l
      | _ ->
        let m = match t with
          | None -> 0
          | Some { S.value = (S.Tuple l) ; _} -> List.length l
          | Some _ -> 1
        in
        error place "The constructor %s expects %d argument(s), but is applied here to %d argument(s)" x n m
    in
    let args = List.map (fun t -> t.S.place, cook_term env t) args in
    List.iter2
      (fun (place, (ty, _)) ety -> check_unify place env ty ety) args cargs;
    T.Tident tname, T.Constructor (catom, List.map (fun (_, (_, t)) -> t) args)


and cook_let env recursive x t =
  match recursive, t with
  | S.NonRecursive, t ->
    let ty, t = cook_term env t in
    let env, x = add_gen x ty env in
    (env, x, t)
  | S.Recursive, { S.value = S.Lam (y, t) ; _ } ->
    let tv = T.Tvar (TV.create ()) in
    let ty, x1, y, nt =
      let env, x = add x tv env in
      let tv1 = T.Tvar (TV.create ()) in
      let env, y = add y tv1 env in
      let ty, nt = cook_term env t in
      T.Tarrow (tv1, ty), x, y, nt
    in
    check_unify t.S.place env ty tv;
    let env, x2 = add_gen x ty env in
    (env, x2, T.Lam (T.Self x1, y, nt))
  | _, { S.place ; _} ->
    error place
      "the right-hand side of 'let rec' must be a lambda-abstraction"

let rec cook_type env { S.place ; S.value } =
  match value with
  | S.TVar x -> begin
    match Smap.find x env.type_bindings with
    | n -> T.Tident n
    | exception Not_found -> error place "Unbound type: %s" x
    end
  | S.TArrow (t1, t2) ->
    T.Tarrow (cook_type env t1, cook_type env t2)
  | S.TTuple l ->
    T.Tproduct (List.map (cook_type env) l)

let rec cook_program env = function
  | { S.value = S.DTerm t ; _ } :: p ->
    let a = Atom.fresh "_" in
    let nt = snd (cook_term env t) in
    T.Let (a, nt, cook_program env p)
  | { S.value = S.DLet (recursive, x, t) ; _ } :: p ->
    let env, x, nt = cook_let env recursive x t in
    T.Let (x, nt, cook_program env p)
  | { S.value = S.DTypeSynonym (x, t) ; _} :: p ->
    let n = Atom.fresh x in
    let nenv = { env with
      type_bindings = Smap.add x n env.type_bindings ;
      type_defs = Atom.Map.add n (TTypeSynonym (cook_type env t))
          env.type_defs ;
    } in
    cook_program nenv p
  | { S.value = S.DNewType (x, l) ; _} :: p ->
    let n = Atom.fresh x in
    let env1 = { env with type_bindings = Smap.add x n env.type_bindings } in
    let constructors = List.map
        (fun { S.value = (name, r) ; _ } ->
           (name, Atom.fresh name, List.map (cook_type env1) r)) l in
    let env2 = { env with
      type_defs = Atom.Map.add n (TBaseType n) env.type_defs ;
      constructor_bindings = List.fold_left
          (fun cbinds (name, atom, _) -> Smap.add name atom cbinds)
          env.constructor_bindings constructors ;
      constructor_defs = List.fold_left
          (fun cdefs (_, name, types) -> Atom.Map.add name (n, types) cdefs)
          env.constructor_defs constructors ;
    } in
    cook_program env2 p
  | [] -> T.Lit 0

let cook_program = cook_program base_env
