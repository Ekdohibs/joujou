open Error

(* The source calculus. *)
module S = RawLambda
(* The target calculus. *)
module T = Lambda
module TyC = T.TyC
module TyS = T.TyS
module TyCSet = T.TyCSet
module TySSet = T.TySSet
module TySPSet = T.TySPSet

let disable_type_checking = ref false
(*
let ( <|> ) a b =
  let rec aux a b r =
    if b <= a then r else aux a (b - 1) ((b - 1) :: r)
  in aux a b []
*)

let builtin_int_id = Atom.fresh "int"
let builtin_int_pos = T.ident true builtin_int_id
let builtin_int_neg = T.ident false builtin_int_id

(*
let head_merge polarity head1 head2 =
  AHSet.union head1 head2

let merge_st (polarity1, head1, nxt1) (polarity2, head2, nxt2) =
  assert (polarity1 = polarity2);
  (polarity1, head_merge polarity1 head1 head2,
   ALMap.merge (fun _ t1 t2 ->
       match t1, t2 with
       | None, None -> None
       | None, Some t | Some t, None -> Some t
       | Some t1, Some t2 -> Some (ISet.union t1 t2)) nxt1 nxt2)

let to_aut polarity ty =
  let open T in
  let aut = { data = Hashtbl.create 17 ; num_states = 0 } in
  let eps = Hashtbl.create 17 in
  let vs = Hashtbl.create 17 in
  let add_eps q1 q2 =
    Hashtbl.replace eps q1
      (ISet.add q2 (try Hashtbl.find eps q1 with Not_found -> ISet.empty))
  in
  let new_state () =
    let n = aut.num_states in
    aut.num_states <- n + 1;
    n
  in
  let rec walk polarity ty =
    match Ty.head ty with
    | Tident name ->
      let n = new_state () in
      let nxt = ALMap.empty in
      Hashtbl.add aut.data n (polarity, AHSet.singleton (HIdent name), nxt);
      n
    | Tarrow (t1, _, t2) ->
      let q1 = walk (not polarity) t1 in
      let q2 = walk polarity t2 in
      let n = new_state () in
      let nxt = from_bindings [
          LArrowsrc, (ISet.singleton q1);
          LArrowdst, (ISet.singleton q2);
        ] in
      Hashtbl.add aut.data n (polarity, AHSet.singleton HArrow, nxt);
      n
    | Tbot ->
      assert polarity;
      let n = new_state () in
      Hashtbl.add aut.data n (polarity, AHSet.empty, ALMap.empty);
      n
    | Ttop ->
      assert (not polarity);
      let n = new_state () in
      Hashtbl.add aut.data n (polarity, AHSet.empty, ALMap.empty);
      n
    | Tjoin (t1, t2) ->
      assert polarity;
      let n = new_state () in
      Hashtbl.add aut.data n (polarity, AHSet.empty, ALMap.empty);
      add_eps n (walk polarity t1);
      add_eps n (walk polarity t2);
      n
    | Tmeet (t1, t2) ->
      assert (not polarity);
      let n = new_state () in
      Hashtbl.add aut.data n (polarity, AHSet.empty, ALMap.empty);
      add_eps n (walk polarity t1);
      add_eps n (walk polarity t2);
      n
    | Tproduct l ->
      let l = List.map (walk polarity) l in
      let n = new_state () in
      let arity = List.length l in
      let nxt = from_bindings (List.mapi
        (fun i q -> (LTuple (arity, i), ISet.singleton q)) l) in
      Hashtbl.add aut.data n (polarity, AHSet.singleton (HTuple arity), nxt);
      n
    | Trec (tv, t1) ->
      let n = new_state () in
      Hashtbl.add vs tv.id n;
      Hashtbl.add aut.data n (polarity, AHSet.empty, ALMap.empty);
      add_eps n (walk polarity t1);
      n
    | Tvar tv ->
      try
        let n = Hashtbl.find vs tv.id in
        let (pol, _, _) = Hashtbl.find aut.data n in
        assert (polarity = pol);
        n
      with Not_found ->
        let n = new_state () in
        Hashtbl.add aut.data n
          (polarity, AHSet.singleton (HVar tv.id), ALMap.empty);
        n
  in
  let root = walk polarity ty in
  let seen = Hashtbl.create 17 in
  let rec ewalk q =
    if not (Hashtbl.mem seen q) then begin
      Hashtbl.add seen q ();
      let data = Hashtbl.find aut.data q in
      let epn = try Hashtbl.find eps q with Not_found -> ISet.empty in
      ISet.iter ewalk epn;
      let data = ISet.fold (fun q2 data ->
          merge_st data (Hashtbl.find aut.data q2)) epn data
      in
      Hashtbl.replace aut.data q data
    end
  in
  Hashtbl.iter (fun q _ -> ewalk q) aut.data;
  (root, aut)

let aut_to_type make_var (q, aut) =
  let open T in
  let seen = Hashtbl.create 17 in
  let jm_all polarity =
    if polarity then List.fold_left tjoin Tbot
    else List.fold_left tmeet Ttop
  in
  let rec walk q =
    let polarity, head, nxt = Hashtbl.find aut.data q in
    if Hashtbl.mem seen q then begin
      match Hashtbl.find seen q with
      | None -> let tv = TV.create () in
        Hashtbl.replace seen q (Some tv);
        Tvar tv
      | Some tv -> Tvar tv
    end else begin
      Hashtbl.add seen q None;
      let head = AHSet.elements head in
      let nty = List.map (function
          | HVar id -> Tvar (make_var id)
          | HIdent n -> Tident n
          | HArrow ->
            let src = List.map walk
                (ISet.elements (ALMap.find LArrowsrc nxt)) in
            let dst = List.map walk
                (ISet.elements (ALMap.find LArrowdst nxt)) in
            Tarrow (jm_all (not polarity) src, Rempty, jm_all polarity dst)
          | HTuple arity ->
            let l = List.map (fun i ->
                jm_all polarity (List.map walk
                  (ISet.elements (ALMap.find (LTuple (arity, i)) nxt)))
            ) (0 <|> arity) in
            Tproduct l
        ) head in
      let ty = jm_all polarity nty in
      let r = match Hashtbl.find seen q with
        | None -> ty
        | Some tv -> Trec(tv, ty)
      in
      Hashtbl.remove seen q;
      r
    end
  in
  walk q

let var_maker () =
  let vars = Hashtbl.create 17 in
  let make_var id =
    try Hashtbl.find vars id
    with Not_found ->
      let v = TV.create () in
      Hashtbl.add vars id v;
      v
  in
  make_var

let from_aut aut =
  aut_to_type (var_maker ()) aut
*)

type scheme = {
  (* First place where the variable was used, for error reporting. *)
  hypotheses : (TyS.t * place) Atom.Map.t ;
  typ : TyS.t ;
}

type binding =
  | BScheme of scheme
  | BInfer

type typedef =
  | TBaseType of Atom.atom
  | TTypeSynonym of TyS.t * TyS.t (* positive, negative *)

module Smap = Map.Make(String)
type env = {
  bindings : (binding * Atom.atom) Smap.t ;
  (*  fvars : TVSet.t ; *)
  type_bindings : Atom.atom Smap.t ;
  type_defs : typedef Atom.Map.t ;
  constructor_bindings : Atom.atom Smap.t ;
  constructor_defs :
    (Atom.atom * (TyS.t * TyS.t) list * int * bool) Atom.Map.t ;
  effect_bindings : Atom.atom Smap.t;
  effect_defs : ((TyS.t * TyS.t) option * (TyS.t * TyS.t) * int) Atom.Map.t ;
  free_effect_tag : int ;
}

let base_env = {
  bindings = Smap.empty ;
  (*  fvars = TVSet.empty ; *)
  type_bindings = Smap.singleton "int" builtin_int_id ;
  type_defs = Atom.Map.singleton builtin_int_id (TBaseType builtin_int_id) ;
  constructor_bindings = Smap.empty ;
  constructor_defs = Atom.Map.empty ;
  effect_bindings = Smap.empty ;
  effect_defs = Atom.Map.empty ;
  free_effect_tag = 0 ;
}

let print_scheme ff { hypotheses ; typ } =
  let l = typ :: (List.map (fun (_, (st, _)) -> st)
                    (Atom.Map.bindings hypotheses)) in
  let st = T.prepare_printing l in
  Format.fprintf ff "[@[<hov 2>";
  List.iteri (fun i (a, (ty, _)) ->
      if i > 0 then Format.fprintf ff ",@ ";
      Format.fprintf ff "%s : %a" (Atom.hint a) (T.print_tys st 0) ty
    ) (Atom.Map.bindings hypotheses);
  Format.fprintf ff "@]] %a" (T.print_tys st 0) typ

let rec resolve env polarity t =
  match t with
  | TyC.Tident n ->
    (match Atom.Map.find n env.type_defs with
     | TTypeSynonym (typ, tyn) ->
       let q = T.copy_one (if polarity then typ else tyn) in
       resolve_all env polarity q.TyS.constructors
     | TBaseType n -> TyCSet.singleton polarity t)
  | t -> TyCSet.singleton polarity t

and resolve_all env polarity ts =
  TyCSet.map_flatten (resolve env) polarity ts

let maybe_resolve env polarity1 polarity2 tc1 tc2 =
  if TyCSet.need_resolve polarity1 polarity2 tc1 tc2 then
    resolve_all env polarity1 tc1, resolve_all env polarity2 tc2
  else
    tc1, tc2

let cmerge env polarity tc1 tc2 =
  let tc1, tc2 = maybe_resolve env polarity polarity tc1 tc2 in
  TyCSet.merge polarity tc1 tc2

let unify_hyp env hp1 hp2 =
  Atom.Map.merge (fun _ ty1 ty2 ->
      match ty1, ty2 with
      | None, None -> None
      | None, Some ty | Some ty, None -> Some ty
      | Some (ty1, place1), Some (ty2, _) ->
        let open TyS in
        let w = create false in
        TySSet.iter (add_flow_edge w) (TySSet.union ty1.flow ty2.flow);
        w.constructors <- cmerge env false ty1.constructors ty2.constructors;
        Some (w, place1)
  ) hp1 hp2

let scheme_merge env q1 q2 =
  let open TyS in
  assert (q1.polarity = q2.polarity);
  let qs = TySSet.diff q2.flow q1.flow in
  TySSet.iter (add_flow_edge q1) qs;
  q1.constructors <- cmerge env q1.polarity q1.constructors q2.constructors

exception BiUnificationFailure of TyC.t * TyC.t

let biunification_error t1 t2 =
  raise (BiUnificationFailure (t1, t2))

let rec biunify_tys env t qp qm =
  if not (TySPSet.mem (qp, qm) !t) then begin
    t := TySPSet.add (qp, qm) !t;
    assert (qp.TyS.polarity && not qm.TyS.polarity);
    TySSet.iter (fun q -> scheme_merge env q qp) qm.TyS.flow;
    TySSet.iter (fun q -> scheme_merge env q qm) qp.TyS.flow;
    let qmc, qpc = maybe_resolve env false true
        qm.TyS.constructors qp.TyS.constructors in
    List.iter (fun tp ->
      List.iter (fun tm ->
        biunify_tyc env t tp tm
      ) qmc;
    ) qpc;
  end

and biunify_tyss env t qps qms =
  TySSet.iter (fun qp ->
    TySSet.iter (fun qm ->
      biunify_tys env t qp qm
    ) qms
  ) qps

and biunify_tyc env t tp tm =
  let open TyC in
  match tp, tm with
  | Tident n1, Tident n2 ->
    if not (Atom.equal n1 n2) then
      biunification_error tp tm
  | Tarrow (tpa, tpb), Tarrow (tma, tmb) ->
    biunify_tyss env t tma tpa;
    biunify_tyss env t tpb tmb
  | Tproduct l1, Tproduct l2 ->
    if List.length l1 = List.length l2 then
      List.iter2 (biunify_tyss env t) l1 l2
    else
      biunification_error tp tm
  | _, _ -> biunification_error tp tm

let biunify env = biunify_tys env (ref TySPSet.empty)

let check_biunify_msg msg place env t1 t2 =
  if not !disable_type_checking then
    try biunify env t1 t2 with
    | BiUnificationFailure (ty1, ty2) ->
      let st = T.prepare_printing
          ([t1; t2] @
           TySSet.(elements (union (T.tyc_succ ty1) (T.tyc_succ ty2))))
      in
      error place msg (T.print_tys st 0) t1 (T.print_tys st 0) t2
        (T.print_tyc st 0 true) ty1 (T.print_tyc st 0 false) ty2

let check_biunify =
  check_biunify_msg "This expression has type %a but was expected of type %a\nThe type %a is not a subtype of the type %a"

let add_bound id a env =
  { env with bindings = Smap.add id (BInfer, a) env.bindings }

let add id env =
  let a = Atom.fresh id in
  add_bound id a env, a

let add_gen id scheme env =
  let a = Atom.fresh id in
(*  let fv = fvars_scheme scheme in
    TVSet.iter TV.lock_t fv; *)
  let nenv = { env with bindings = Smap.add id (BScheme scheme, a) env.bindings } in
  (nenv, a)

let copy_scheme { hypotheses ; typ } =
  let l = typ :: (List.map (fun (_, (st, _)) -> st)
                    (Atom.Map.bindings hypotheses)) in
  let st = T.prepare_copy l in
  {
    hypotheses = Atom.Map.map
        (fun (ty, place) -> (T.copy st ty, place)) hypotheses ;
    typ = T.copy st typ ;
  }

let find place id env =
  let (sc, a) = Smap.find id env.bindings in
  match sc with
  | BScheme sc -> copy_scheme sc, a
  | BInfer ->
    let typ, tyn = TyS.create_flow_pair () in
    let sc = {
      hypotheses = Atom.Map.singleton a (tyn, place) ;
      typ = typ ;
    } in
    sc, a

let unify_hyp_many env l =
  List.fold_left (unify_hyp env) Atom.Map.empty l

let rec cook_term env { S.place ; S.value } =
  match value with
  | S.Var x -> begin
    match find place x env with
    | sc, a -> sc, T.Var a
    | exception Not_found -> error place "Unbound variable: %s" x
    end
  | S.Lam (x, t) ->
    let nenv, x = add x env in
    let sc, t = cook_term nenv t in
    let nh, src =
      try
        let ty, _ = Atom.Map.find x sc.hypotheses in
        Atom.Map.remove x sc.hypotheses, Some ty
      with Not_found ->
        sc.hypotheses, None
    in
    let w = T.arrow_option true src sc.typ in
    let nsc = {
      hypotheses = nh ;
      typ = w ;
    } in
    nsc, T.Lam (T.NoSelf, x, t)
  | S.App (t1, t2) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let (wp, wn) = TyS.create_flow_pair () in
    let w = T.arrow false sc2.typ wn in
    let nh = unify_hyp env sc1.hypotheses sc2.hypotheses in
    check_biunify t1.S.place env sc1.typ w;
    let nsc = {
      hypotheses = nh ;
      typ = wp ;
    } in
    nsc, T.App (nt1, nt2)
  | S.Lit i ->
    let w = T.ident true builtin_int_id in
    let sc = {
      hypotheses = Atom.Map.empty ;
      typ = w ;
    } in
    sc, T.Lit i
  | S.BinOp (t1, op, t2) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let nh = unify_hyp env sc1.hypotheses sc2.hypotheses in
    let w1 = T.ident true builtin_int_id in
    let w2 = T.ident false builtin_int_id in
    check_biunify t1.S.place env sc1.typ w2;
    check_biunify t2.S.place env sc2.typ w2;
    let sc = {
      hypotheses = nh ;
      typ = w1 ;
    } in
    sc, T.BinOp (nt1, op, nt2)
  | S.Print t ->
    let sc, nt = cook_term env t in
    let w1 = T.ident false builtin_int_id in
    check_biunify t.S.place env sc.typ w1;
    (* TODO: print produces io effect *)
    sc, T.Print nt
  | S.Let (recursive, x, t1, t2) ->
    let nenv, x, sc1, nt1 = cook_let env recursive x t1 in
    (* Format.eprintf "val %s : @[<hv>%a@]@." (Atom.hint x) print_scheme sc1; *)
    let sc2, nt2 = cook_term nenv t2 in
    let nh = unify_hyp env sc1.hypotheses sc2.hypotheses in
    let nsc = {
      hypotheses = nh ;
      typ = sc2.typ ;
    } in
    nsc, T.Let (x, nt1, nt2)
  | S.IfZero (t1, t2, t3) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let sc3, nt3 = cook_term env t3 in
    let nh = unify_hyp env sc1.hypotheses
        (unify_hyp env sc2.hypotheses sc3.hypotheses) in
    let (wp, wn) = TyS.create_flow_pair () in
    let w = T.ident false builtin_int_id in
    check_biunify t1.S.place env sc1.typ w;
    check_biunify t2.S.place env sc2.typ wn;
    check_biunify t3.S.place env sc3.typ wn;
    let nsc = {
      hypotheses = nh ;
      typ = wp ;
    } in
    nsc, T.IfZero (nt1, nt2, nt3)
  | S.Tuple l ->
    let l = List.map (cook_term env) l in
    let nh = unify_hyp_many env (List.map (fun (sc, _) -> sc.hypotheses) l) in
    let w = T.product true (List.map (fun (sc, _) -> sc.typ) l) in
    let nsc = {
      hypotheses = nh ;
      typ = w ;
    } in
    nsc, (T.Tuple (List.map snd l))
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
    let nh = unify_hyp_many env
        (List.map (fun (_, (sc, _)) -> sc.hypotheses) args) in
    List.iter2 (fun (place, (sc, _)) (_, enty) ->
        check_biunify place env sc.typ (T.copy_one enty)
    ) args cargs;
    let nt =
      if is_effect then
        let (_, (npt, _), _) = Atom.Map.find tname env.effect_defs in
        T.copy_one npt
      else
        T.ident true tname
    in
    let nsc = {
      hypotheses = nh ;
      typ = nt ;
    } in
    nsc, T.Constructor ((catom, ctag, is_effect),
                        List.map (fun (_, (_, t)) -> t) args)
  | S.Match (t, l) ->
    let sc, nt = cook_term env t in
    let rtyp, rtyn = TyS.create_flow_pair () in
    let nl = List.map (fun (p, t1) ->
      let np, dv = cook_pattern_or_effect env sc.typ rtyp p in
      let nenv = Smap.fold (fun x (a, t) env -> add_bound x a env) dv env in
      let sc1, nt1 = cook_term nenv t1 in
      check_biunify t1.S.place env sc1.typ rtyn;
      let nh = Smap.fold (fun _ (a, t) h ->
          try
            let ty, place = Atom.Map.find a h in
            check_biunify place env t ty;
            Atom.Map.remove a h
          with Not_found -> h
      ) dv sc1.hypotheses in
      (nh, (np, nt1))
    ) l in
    let nsc = {
      hypotheses = List.fold_left
          (fun h1 (h2, _) -> unify_hyp env h1 h2) sc.hypotheses nl ;
      typ = rtyp ;
    } in
    nsc, T.Match (nt, List.map snd nl)

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
    let ty1, (_, ty2n), _ = Atom.Map.find ename env.effect_defs in
    if not is_effect then
      error place "This constructor is a value constructor, not an effect constructor";
    let np, dv =
      match p, ty1 with
      | None, None -> T.PConstructor ((catom, ctag, true), []), Smap.empty
      | Some p, Some (ty1p, _) ->
        let np, dv = cook_pattern env Smap.empty ty1p p in
        if Smap.mem k dv then
          error p.S.place "The variable %s is already bound in this matching" k;
        T.PConstructor ((catom, ctag, true), [np]), dv
      | None, Some _ ->
        error place "The effect constructor %s expects 1 argument, but is applied here to 0 arguments" c
      | Some _, None ->
        error place "The effect constructor %s expects 0 arguments, but is applied here to 1 argument" c
    in
    (* TODO *)
    let kty = T.arrow true ty2n rty in
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
(*        (if not !disable_type_checking then
          try unify env ty1 ty2 with
          | UnificationFailure (ty1_, ty2_) ->
            error place "The variable %s on the left-hand side of this | pattern has type %s but on the right-hand side it has type %s\nThe type %s is incompatible with the type %s" x (T.show_typ (Ty.canon ty1)) (T.show_typ (Ty.canon ty2)) (T.show_typ (Ty.canon ty1_)) (T.show_typ (Ty.canon ty2_))); *)
        let wp, wn = TyS.create_flow_pair () in
        check_biunify place env ty1 wn;
        check_biunify place env ty2 wn;
        Some (a1, wp)
      | _ -> error place "Variable %s must appear on both sides of this | pattern" x
    ) dv1 dv2 in
    np, dv
  | S.PTuple l ->
    let ws = List.map (fun _ -> TyS.create_flow_pair ()) l in
    check_biunify_msg "A pattern was expected which matches values of type %a but this pattern matches values of type %a\nThe type %a is not a subtype of the type %a" place env ty (T.product false (List.map snd ws));
    let nl = List.map2 (cook_pattern env mapped_vars) (List.map fst ws) l in
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
    check_biunify_msg "A pattern was expected which matches values of type %a but this pattern matches values of type %a\nThe type %a is not a subtype of the type %a" place env ty (T.ident false tname);
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
    let nl = List.map2 (cook_pattern env mapped_vars) (List.map fst cargs) args in
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
    let sc, t = cook_term env t in
    let nenv, nx = add_gen x sc env in
    (nenv, nx, copy_scheme sc, t)
  | S.Recursive, { S.value = S.Lam (y, t) ; _ } ->
    let sc, nx, ny, nt =
      let nenv, nx = add x env in
      let nenv, ny = add y nenv in
      let sc, nt = cook_term nenv t in
      let nh, src =
        try
          let ty, _ = Atom.Map.find ny sc.hypotheses in
          Atom.Map.remove ny sc.hypotheses, Some ty
        with Not_found ->
          sc.hypotheses, None
      in
      let w = T.arrow_option true src sc.typ in
      let nh =
        try
          let ty, _ = Atom.Map.find nx nh in
          check_biunify t.S.place nenv w ty;
          Atom.Map.remove nx nh
        with Not_found -> nh
      in
      let nsc = {
        hypotheses = nh ;
        typ = w ;
      } in
      nsc, nx, ny, nt
    in
    let nenv, nx2 = add_gen x sc env in
    (nenv, nx2, sc, T.Lam (T.Self nx, ny, nt))
  | _, { S.place ; _} ->
    error place
      "the right-hand side of 'let rec' must be a lambda-abstraction"

let rec cook_type env polarity { S.place ; S.value } =
  match value with
  | S.TVar x -> begin
    match Smap.find x env.type_bindings with
    | n -> T.ident polarity n
    | exception Not_found -> error place "Unbound type: %s" x
    end
  | S.TArrow (t1, t2) -> (* TODO *)
    T.arrow polarity
      (cook_type env (not polarity) t1)
      (cook_type env polarity t2)
  | S.TTuple l ->
    T.product polarity
      (List.map (cook_type env polarity) l)
(*
let print_schema ff { vars ; typ } =
  let fv = Ty.fvars typ in
  Ty.print (TV.get_print_names fv vars) 0 ff typ
*)

let rec cook_program env = function
  | { S.value = S.DTerm t ; _ } :: p ->
    let a = Atom.fresh "_" in
    let sc, nt = cook_term env t in
    assert (Atom.Map.is_empty sc.hypotheses);
    (* unify_row row T.Rempty; (* TODO allow io *) *)
    T.Let (a, nt, cook_program env p)
  | { S.value = S.DLet (recursive, x, t) ; _ } :: p ->
    let env, nx, sc, nt = cook_let env recursive x t in
    (* unify_row row T.Rempty; (* TODO allow io *) *)
    assert (Atom.Map.is_empty sc.hypotheses);
    Format.eprintf "val %s : @[<hv>%a@]@." x print_scheme sc;
    T.Let (nx, nt, cook_program env p)
  | { S.value = S.DTypeSynonym (x, t) ; _ } :: p ->
    let n = Atom.fresh x in
    let nenv = { env with
      type_bindings = Smap.add x n env.type_bindings ;
      type_defs = Atom.Map.add n
          (TTypeSynonym (cook_type env true t, cook_type env false t))
          env.type_defs ;
    } in
    cook_program nenv p
  | { S.value = S.DNewType (x, l) ; _ } :: p ->
    let n = Atom.fresh x in
    let env1 = { env with type_bindings = Smap.add x n env.type_bindings } in
    let constructors = List.map
        (fun { S.value = (name, r) ; _ } ->
           (name, Atom.fresh name,
            List.map (fun t ->
                cook_type env1 true t, cook_type env1 false t) r)
        ) l in
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
    let ty1 = match t1 with
      | None -> None
      | Some t1 -> Some (cook_type env true t1, cook_type env false t1)
    in
    let ty2 = (cook_type env true t2, cook_type env false t2) in
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
