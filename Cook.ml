open Error

(* The source calculus. *)
module S = RawLambda
(* The target calculus. *)
module T = Lambda
module TV = T.TV
module Ty = T.Ty
module Row = T.Row
module TVSet = T.TVSet

let disable_type_checking = ref false

type schema = {
  vars : TVSet.t ;
  typ : Ty.t ;
}

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
  | Tarrow (ta, r, tb) -> occur var ta || occur var tb
  | Tproduct l -> List.exists (occur var) l
  | Tvar tv -> TV.equal (TV.of_typevar tv) var

let rec resolve env t =
  let open T in
  match (Ty.head t) with
  | Tident n ->
    (match Atom.Map.find n env.type_defs with
     | TTypeSynonym t -> resolve env t
     | TBaseType n -> Tident n)
  | t -> t

let rec open_row dir r =
  let open T in
  match (Row.head r) with
  | Rempty -> if dir then Rvar (TV.create ()) else Rempty
  | Reffect (name, r) -> Reffect (name, open_row dir r)
  | Rvar _ -> r

let rec open_type dir t =
  let open T in
  match (Ty.head t) with
  | Tident n -> Tident n (* TODO: this needs to be opened *)
  | Tproduct l -> Tproduct (List.map (open_type dir) l)
  | Tvar tv -> Tvar tv
  | Tarrow (t1, r, t2) ->
    Tarrow (open_type (not dir) t1, open_row dir r, open_type dir t2)

let rec unclosable_row dir r =
  let open T in
  match (Row.head r) with
  | Rempty -> TVSet.empty
  | Reffect (name, r) -> unclosable_row dir r
  | Rvar tv -> if dir then TVSet.empty else TVSet.singleton (TV.of_rowvar tv)

let rec unclosable_type dir t =
  let open T in
  match (Ty.head t) with
  | Tident n -> TVSet.empty (* TODO: what happens? *)
  | Tproduct l ->
    List.map (unclosable_type dir) l |> List.fold_left TVSet.union TVSet.empty
  | Tvar _ -> TVSet.empty
  | Tarrow (t1, r, t2) ->
    TVSet.union (unclosable_type (not dir) t1)
      (TVSet.union
         (unclosable_row dir r) (unclosable_type dir t2))

let rec close_row unc r =
  let open T in
  match (Row.head r) with
  | Rempty -> Rempty
  | Rvar tv -> if TVSet.mem (TV.of_rowvar tv) unc then Rvar tv else Rempty
  | Reffect (name, r) -> Reffect (name, close_row unc r)

let rec close_type unc t =
  let open T in
  match (Ty.head t) with
  | Tident n -> Tident n (* TODO: hmmmm *)
  | Tproduct l ->
    Tproduct (List.map (close_type unc) l)
  | Tvar tv -> Tvar tv
  | Tarrow (t1, r, t2) ->
    Tarrow (close_type unc t1, close_row unc r, close_type unc t2)

let rec row_to_set r =
  let open T in
  match Row.head r with
  | Rempty -> Atom.Set.empty, None
  | Rvar tv -> Atom.Set.empty, Some tv
  | Reffect (name, r) ->
    let s, v = row_to_set r in
    Atom.Set.add name s, v

let extend_row v s =
  Atom.Set.fold (fun name v ->
    assert (v.T.def = None);
    let nv = TV.create () in
    v.T.def <- Some (T.Reffect (name, T.Rvar nv));
    nv
  ) s v

let rec unify_row r1 r2 =
  let s1, v1 = row_to_set r1 in
  let s2, v2 = row_to_set r2 in
  let s12 = Atom.Set.diff s1 s2 in
  let s21 = Atom.Set.diff s2 s1 in
  let v2 =
    if not (Atom.Set.is_empty s12) then
      match v2 with
      | None -> assert false (* TODO: nice error msg *)
      | Some v2 ->
        Some (extend_row v2 s12)
    else v2
  in
  let v1 =
    if not (Atom.Set.is_empty s21) then
      match v1 with
      | None -> assert false (* TODO: nice error msg *)
      | Some v1 ->
        Some (extend_row v1 s21)
    else v1
  in
  match v1, v2 with
  | None, None -> ()
  | None, Some v | Some v, None -> v.T.def <- Some (T.Rempty)
  | Some v1, Some v2 ->
    if TV.eq v1 v2 then ()
    else v1.T.def <- Some (T.Rvar v2)

let rec unify env t1 t2 =
  let open T in
  match (resolve env t1), (resolve env t2) with
  | Tident n1, Tident n2 ->
    if not (Atom.equal n1 n2) then
      unification_error t1 t2
  | Tarrow (t1a, r1, t1b), Tarrow (t2a, r2, t2b) ->
    unify env t1a t2a; unify env t1b t2b; unify_row r1 r2
  | Tproduct l1, Tproduct l2 ->
    if List.length l1 <> List.length l2 then
      unification_error t1 t2
    else
      List.iter2 (unify env) l1 l2
  | Tvar tv1, Tvar tv2 ->
    if not (TV.eq tv1 tv2) then
      tv1.def <- Some t2
  | Tvar tv, t | t, Tvar tv ->
    if occur (TV.of_typevar tv) t then
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

let add_bound id a typ env =
  let fv = Ty.fvars typ in
  let nenv = { env with
    bindings = Smap.add id
        ({ vars = TVSet.empty ; typ = typ }, a)
        env.bindings ;
    fvars = TVSet.union (TV.recompute_fvars env.fvars) fv ;
  } in
  nenv

let add id typ env =
  let a = Atom.fresh id in
  add_bound id a typ env, a

let add_gen id typ env =
  let fv = Ty.fvars typ in
  let a = Atom.fresh id in
  let nfv = TV.recompute_fvars env.fvars in
  let vars = TVSet.diff fv nfv in
(*  let unc = TVSet.union nfv (unclosable_type true typ) in
    let typ = close_type unc typ in *)
  let nenv = { env with
    bindings = Smap.add id
        ({ vars = vars ; typ = typ }, a)
        env.bindings ;
    fvars = nfv ;
  } in
  (nenv, a)

let find id env =
  let ({ vars = vars ; typ = typ }, a) = Smap.find id env.bindings in
  (* open_type true (Ty.refresh vars typ), a *)
  Ty.refresh vars typ, a

let rec cook_term env { S.place ; S.value } =
  match value with
  | S.Var x -> begin
    match find x env with
    | typ, a -> typ, T.Rvar (TV.create()), T.Var a
    | exception Not_found -> error place "Unbound variable: %s" x
    end
  | S.Lam (x, t) ->
    let tv = T.Tvar (TV.create ()) in
    let env, x = add x tv env in
    let typ, row, t = cook_term env t in
    T.Tarrow (tv, row, typ), T.Rvar (TV.create ()), T.Lam (T.NoSelf, x, t)
  | S.App (t1, t2) ->
    let ty1, row1, nt1 = cook_term env t1 in
    let ty2, row2, nt2 = cook_term env t2 in
    unify_row row1 row2;
    let tv = T.Tvar (TV.create ()) in
    let rv = T.Rvar (TV.create ()) in
    check_unify t1.S.place env ty1 (T.Tarrow (ty2, rv, tv));
    unify_row row1 rv;
    tv, rv, T.App (nt1, nt2)
  | S.Lit i ->
    builtin_int, T.Rvar (TV.create ()), T.Lit i
  | S.BinOp (t1, op, t2) ->
    let ty1, row1, nt1 = cook_term env t1 in
    let ty2, row2, nt2 = cook_term env t2 in
    check_unify t1.S.place env ty1 builtin_int;
    check_unify t2.S.place env ty2 builtin_int;
    unify_row row1 row2;
    builtin_int, row1, T.BinOp (nt1, op, nt2)
  | S.Print t ->
    let ty, row, nt = cook_term env t in
    check_unify t.S.place env ty builtin_int;
    (* TODO: print produces io effect *)
    builtin_int, row, T.Print nt
  | S.Let (recursive, x, t1, t2) ->
    let env, x, nt1, _, row1 = cook_let env recursive x t1 in
    let ty2, row2, nt2 = cook_term env t2 in
    unify_row row1 row2;
    ty2, row1, T.Let (x, nt1, nt2)
  | S.IfZero (t1, t2, t3) ->
    let ty1, row1, nt1 = cook_term env t1 in
    let ty2, row2, nt2 = cook_term env t2 in
    let ty3, row3, nt3 = cook_term env t3 in
    check_unify t1.S.place env ty1 builtin_int;
    check_unify t3.S.place env ty3 ty2;
    unify_row row1 row2;
    unify_row row1 row3;
    ty2, row1, T.IfZero (nt1, nt2, nt3)
  | S.Tuple l ->
    let l = List.map (cook_term env) l in
    let row = T.Rvar (TV.create ()) in
    List.iter (fun (_, r, _) -> unify_row r row) l;
    T.Tproduct (List.map (fun (ty, _, _) -> ty) l), row,
      (T.Tuple (List.map (fun (_, _, nt) -> nt) l))
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
    let row = T.Rvar (TV.create ()) in
    List.iter (fun (_, (_, r, _)) -> unify_row r row) args;
    List.iter2
      (fun (place, (ty, _, _)) ety -> check_unify place env ty ety) args cargs;
    (* TODO: if effect, add to list *)
    let nt =
      if is_effect then
        let (_, nt, _) = Atom.Map.find tname env.effect_defs in nt
      else
        T.Tident tname
    in
    nt, row, T.Constructor ((catom, ctag, is_effect), List.map (fun (_, (_, _, t)) -> t) args)
  | S.Match (t, l) ->
    let ty, row, nt = cook_term env t in
    let rty = T.Tvar (TV.create ()) in
    let row1 = T.Rvar (TV.create ()) in
    let nl = List.map (fun (p, t1) ->
      let np, dv = cook_pattern_or_effect env ty rty p in
      let nenv = Smap.fold (fun x (a, t) env -> add_bound x a t env) dv env in
      let ty1, r, nt1 = cook_term nenv t1 in
      unify_row r row1;
      check_unify t1.S.place env ty1 rty;
      (np, nt1)
    ) l in
    unify_row row row1; (* TODO: handle effects *)
    rty, row1, T.Match (nt, nl)

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
    (* TODO *)
    let kty = T.Tarrow (ty2, T.Rempty, rty) in
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
    let ty, row, t = cook_term env t in
    let env, nx = add_gen x ty env in
    (env, nx, t, fst (Smap.find x env.bindings), row)
  | S.Recursive, { S.value = S.Lam (y, t) ; _ } ->
    let tv = T.Tvar (TV.create ()) in
    let ty, x1, y, nt =
      let env, x = add x tv env in
      let tv1 = T.Tvar (TV.create ()) in
      let env, y = add y tv1 env in
      let ty, row, nt = cook_term env t in
      T.Tarrow (tv1, row, ty), x, y, nt
    in
    check_unify t.S.place env ty tv;
    let env, x2 = add_gen x ty env in
    (env, x2, T.Lam (T.Self x1, y, nt), fst (Smap.find x env.bindings), T.Rvar (TV.create ()))
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
  | S.TArrow (t1, t2) -> (* TODO *)
    T.Tarrow (cook_type env t1, T.Rempty, cook_type env t2)
  | S.TTuple l ->
    T.Tproduct (List.map (cook_type env) l)

let print_schema ff { vars ; typ } =
  let fv = Ty.fvars typ in
  Ty.print (TV.get_print_names fv vars) 0 ff typ

let rec cook_program env = function
  | { S.value = S.DTerm t ; _ } :: p ->
    let a = Atom.fresh "_" in
    let ty, row, nt = cook_term env t in
    unify_row row T.Rempty; (* TODO allow io *)
    T.Let (a, nt, cook_program env p)
  | { S.value = S.DLet (recursive, x, t) ; _ } :: p ->
    let env, nx, nt, ty, row = cook_let env recursive x t in
    unify_row row T.Rempty; (* TODO allow io *)
    Format.eprintf "val %s : @[<hv>%a@]@." x print_schema ty;
    T.Let (nx, nt, cook_program env p)
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
