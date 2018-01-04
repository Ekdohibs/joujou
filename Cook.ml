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
  constructor_defs : (Atom.atom * Ty.t list * int * bool) Atom.Map.t ;
  effect_bindings : Atom.atom Smap. t;
  effect_defs : (Ty.t option * Ty.t * int) Atom.Map.t ;
  free_effect_tag : int ;
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
  effect_bindings = Smap.empty ;
  effect_defs = Atom.Map.empty ;
  free_effect_tag = 0 ;
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

let check_unify_msg msg place env t1 t2 =
  if not !disable_type_checking then
    try unify env t1 t2 with
    | UnificationFailure (ty1, ty2) ->
      error place msg (T.show_typ (Ty.canon t1)) (T.show_typ (Ty.canon t2)) (T.show_typ (Ty.canon ty1)) (T.show_typ (Ty.canon ty2))

let check_unify = check_unify_msg "This expression has type %s but was expected of type %s\nThe type %s is incompatible with the type %s"

let recompute_fvars fv =
  (* If the definitions of some variables changed, then the free variables
     might not be the same. However, the new set of free variables is exactly
     the set of free variables obtained from current definition of the
     previous free variables.
  *)
  TVSet.fold (fun v f -> TVSet.union f (Ty.fvars (T.Tvar v))) fv TVSet.empty

let add_bound id a typ env =
  let fv = Ty.fvars typ in
  let nenv = { env with
    bindings = Smap.add id
        ({ vars = TVSet.empty ; typ = typ }, a)
        env.bindings ;
    fvars = TVSet.union (recompute_fvars env.fvars) fv ;
  } in
  nenv

let add id typ env =
  let a = Atom.fresh id in
  add_bound id a typ env, a

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
    check_unify t3.S.place env ty3 ty2;
    ty2, T.IfZero (nt1, nt2, nt3)
  | S.Tuple l ->
    let l = List.map (cook_term env) l in
    T.Tproduct (List.map fst l), (T.Tuple (List.map snd l))
  | S.Constructor (x, t) ->
    let catom =
      try Smap.find x env.constructor_bindings
      with Not_found -> error place "Unbound constructor: %s" x
    in
    let tname, cargs, ctag, is_effect = Atom.Map.find catom env.constructor_defs in
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
    let nt =
      if is_effect then
        let (_, nt, _) = Atom.Map.find tname env.effect_defs in nt
      else
        T.Tident tname
    in
    nt, T.Constructor ((catom, ctag, is_effect), List.map (fun (_, (_, t)) -> t) args)
  | S.Match (t, l) ->
    let ty, nt = cook_term env t in
    let rty = T.Tvar (TV.create ()) in
    let nl = List.map (fun (p, t1) ->
      let np, dv = cook_pattern_or_effect env ty rty p in
      let nenv = Smap.fold (fun x (a, t) env -> add_bound x a t env) dv env in
      let ty1, nt1 = cook_term nenv t1 in
      check_unify t1.S.place env ty1 rty;
      (np, nt1)
    ) l in
    rty, T.Match (nt, nl)

and cook_pattern_or_effect env ty rty = function
  | S.Pattern p ->
    let p, dv = cook_pattern env Smap.empty ty p in
    T.Pattern p, dv
  | S.Effect ({ S.value = c ; S.place }, p, k) ->
    let catom =
      try Smap.find c env.constructor_bindings
      with Not_found -> error place "Unbound constructor: %s" c
    in
    let ename, _, ctag, is_effect = Atom.Map.find catom env.constructor_defs in
    let ty1, ty2, _ = Atom.Map.find ename env.effect_defs in
    if not is_effect then
      error place "This constructor is a value constructor, not an effect constructor";
    let np, dv =
      match p, ty1 with
      | None, None -> T.PConstructor ((catom, ctag, true), []), Smap.empty
      | Some p, Some ty1 ->
        let np, dv = cook_pattern env Smap.empty ty1 p in
        if Smap.mem k dv then
          error p.S.place "The variable %s is already bound in this matching" k;
        T.PConstructor ((catom, ctag, true), [np]), dv
      | None, Some _ ->
        error place "The effect constructor %s expects 1 argument, but is applied here to 0 arguments" c
      | Some _, None ->
        error place "The effect constructor %s expects 0 arguments, but is applied here to 1 argument" c
    in
    let kty = T.Tarrow (ty2, rty) in
    let kv = Atom.fresh k in
    T.Effect (np, kv), (Smap.add k (kv, kty) dv)

and cook_pattern env mapped_vars ty { S.value ; S.place } =
  match value with
  | S.PVar x ->
    let a = try Smap.find x mapped_vars with Not_found -> Atom.fresh x in
    T.PVar a, Smap.singleton x (a, ty)
  | S.POr (p1, p2) ->
    let np1, dv1 = cook_pattern env mapped_vars ty p1 in
    let mv = Smap.fold (fun x (a, _) mv -> Smap.add x a mv) dv1 mapped_vars in
    let np2, dv2 = cook_pattern env mv ty p2 in
    let np = T.POr (np1, np2) in
    let dv = Smap.merge (fun x def1 def2 ->
      match def1, def2 with
      | None, None -> None
      | Some (a1, ty1), Some (a2, ty2) ->
        assert (Atom.equal a1 a2);
        (if not !disable_type_checking then
          try unify env ty1 ty2 with
          | UnificationFailure (ty1_, ty2_) ->
            error place "The variable %s on the left-hand side of this | pattern has type %s but on the right-hand side it has type %s\nThe type %s is incompatible with the type %s" x (T.show_typ (Ty.canon ty1)) (T.show_typ (Ty.canon ty2)) (T.show_typ (Ty.canon ty1_)) (T.show_typ (Ty.canon ty2_)));
        Some (a1, ty1)
      | _ -> error place "Variable %s must appear on both sides of this | pattern" x
    ) dv1 dv2 in
    np, dv
  | S.PTuple l ->
    let tvs = List.map (fun _ -> T.Tvar (TV.create ())) l in
    check_unify_msg "This pattern matches values of type %s but a pattern was expected which matches values of type %s\nThe type %s is incompatible with the type %s" place env (T.Tproduct tvs) ty;
    let nl = List.map2 (cook_pattern env mapped_vars) tvs l in
    let np = T.PTuple (List.map fst nl) in
    let dv = List.fold_left (fun dv (_, dvi) ->
      Smap.merge (fun x def1 def2 ->
        match def1, def2 with
        | None, None -> None
        | Some (a, ty), None | None, Some (a, ty) -> Some (a, ty)
        | Some _, Some _ ->
          error place "The variable %s is bound several times in this matching" x
      ) dv dvi
    ) Smap.empty nl in
    np, dv
  | S.PConstructor (x, p) ->
    let catom =
      try Smap.find x env.constructor_bindings
      with Not_found -> error place "Unbound constructor: %s" x
    in
    let tname, cargs, ctag, is_effect = Atom.Map.find catom env.constructor_defs in
    if is_effect then
      error place "This constructor is an effect constructor, not a value constructor";
    check_unify_msg "This pattern matches values of type %s but a pattern was expected which matches values of type %s\nThe type %s is incompatible with the type %s" place env (T.Tident tname) ty;
    let n = List.length cargs in
    let args =
      match n, p with
      | 0, None -> []
      | 1, Some p -> [p]
      | 2, Some { S.value = (S.PTuple l) ; _ } -> l
      | _ ->
        let m = match p with
          | None -> 0
          | Some { S.value = (S.PTuple l) ; _} -> List.length l
          | Some _ -> 1
        in
        error place "The constructor %s expects %d argument(s), but is applied here to %d argument(s)" x n m
    in
    let nl = List.map2 (cook_pattern env mapped_vars) cargs args in
    let np = T.PConstructor ((catom, ctag, false), List.map fst nl) in
    let dv = List.fold_left (fun dv (_, dvi) ->
      Smap.merge (fun x def1 def2 ->
        match def1, def2 with
        | None, None -> None
        | Some (a, ty), None | None, Some (a, ty) -> Some (a, ty)
        | Some _, Some _ ->
          error place "The variable %s is bound several times in this matching" x
      ) dv dvi
    ) Smap.empty nl in
    np, dv


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
  | { S.value = S.DTypeSynonym (x, t) ; _ } :: p ->
    let n = Atom.fresh x in
    let nenv = { env with
      type_bindings = Smap.add x n env.type_bindings ;
      type_defs = Atom.Map.add n (TTypeSynonym (cook_type env t))
          env.type_defs ;
    } in
    cook_program nenv p
  | { S.value = S.DNewType (x, l) ; _ } :: p ->
    let n = Atom.fresh x in
    let env1 = { env with type_bindings = Smap.add x n env.type_bindings } in
    let constructors = List.map
        (fun { S.value = (name, r) ; _ } ->
           (name, Atom.fresh name, List.map (cook_type env1) r)) l in
    let env2 = { env1 with
      type_defs = Atom.Map.add n (TBaseType n) env.type_defs ;
      constructor_bindings = List.fold_left
          (fun cbinds (name, atom, _) -> Smap.add name atom cbinds)
          env.constructor_bindings constructors ;
      constructor_defs = snd (List.fold_left
          (fun (i, cdefs) (_, name, types) ->
            (i + 1, Atom.Map.add name (n, types, i, false) cdefs))
          (0, env.constructor_defs) constructors) ;
    } in
    cook_program env2 p
  | { S.value = S.DEffect (x, { S.value = (c, t1, t2) ; _ }) ; _ } :: p ->
    let n = Atom.fresh x in
    let cn = Atom.fresh c in
    let ty1 = match t1 with None -> None | Some t1 -> Some (cook_type env t1) in
    let ty2 = cook_type env t2 in
    let nenv = { env with
      effect_bindings = Smap.add x n env.effect_bindings ;
      effect_defs = Atom.Map.add n (ty1, ty2, env.free_effect_tag) env.effect_defs ;
      free_effect_tag = env.free_effect_tag + 1 ;
      constructor_bindings = Smap.add c cn env.constructor_bindings ;
      constructor_defs = Atom.Map.add cn (n, (match ty1 with None -> [] | Some ty1 -> [ty1]), env.free_effect_tag, true) env.constructor_defs ;
    } in
    cook_program nenv p
  | [] -> T.Lit 0

let cook_program = cook_program base_env
