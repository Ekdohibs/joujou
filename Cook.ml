open Error

(* The source calculus. *)
module S = RawLambda
(* The target calculus. *)
module T = Lambda
(* Alias some modules defined in [Lambda] for quicker access. *)
module TyC = T.TyC
module TyS = T.TyS
module TyE = T.TyE
module TyCSet = T.TyCSet
module TySSet = T.TySSet
module TyESet = T.TyESet
module TySPSet = T.TySPSet

let disable_type_checking = ref false

let builtin_int_id = Atom.fresh "int"
let builtin_io_id = Atom.fresh "io"

type scheme = {
  (* First place where the variable was used, for error reporting. *)
  hypotheses : (TyS.t * place) Atom.Map.t ;
  typ : TyS.t ;
  eff : TyE.t ;
}

type binding =
  | BScheme of scheme
  | BInfer

type inst = TyS.t Atom.Map.t -> TyS.t

type typedef =
  | TBaseType of Atom.atom
  | TTypeSynonym of inst * inst (* positive, negative *)

type tavar =
  | ANone
  | APos of Atom.atom
  | ANeg of Atom.atom
  | APosNeg of Atom.atom * Atom.atom

module Smap = Map.Make(String)
type env = {
  bindings : (binding * Atom.atom) Smap.t ;
  (*  fvars : TVSet.t ; *)
  type_bindings : Atom.atom Smap.t ;
  type_variables : (Atom.atom * Atom.atom) Smap.t ;
  type_variance : tavar list Atom.Map.t ;
  type_defs : typedef Atom.Map.t ;
  constructor_bindings : Atom.atom Smap.t ;
  constructor_defs :
    (Atom.atom * (inst * inst) list * int * bool) Atom.Map.t ;
  effect_bindings : Atom.atom Smap.t;
  effect_defs : ((inst * inst) option * (inst * inst) * int) Atom.Map.t ;
  free_effect_tag : int ;
}

let base_env = {
  bindings = Smap.empty ;
  type_bindings = Smap.singleton "int" builtin_int_id ;
  type_variables = Smap.empty ;
  type_variance = Atom.Map.singleton builtin_int_id [] ;
  type_defs = Atom.Map.singleton builtin_int_id (TBaseType builtin_int_id) ;
  constructor_bindings = Smap.empty ;
  constructor_defs = Atom.Map.empty ;
  effect_bindings = Smap.empty ;
  effect_defs = Atom.Map.empty ;
  free_effect_tag = 0 ;
}

let rec do_instanciate env polarity t vs vas =
  assert (List.length vas = List.length vs);
  let am = List.fold_left2 (fun am v va ->
    match va with
    | ANone -> assert (v = TyC.VNone); am
    | APos xp ->
      let qp = match v with
        | TyC.VNone -> TyS.create polarity
        | TyC.VPos qps -> merge_all env polarity qps
        | _ -> assert false
      in
      assert (qp.TyS.polarity = polarity);
      Atom.Map.add xp qp am
    | ANeg xn ->
      let qn = match v with
        | TyC.VNone -> TyS.create (not polarity)
        | TyC.VNeg qns -> merge_all env (not polarity) qns
        | _ -> assert false
      in
      assert (qn.TyS.polarity = not polarity);
      Atom.Map.add xn qn am
    | APosNeg (xp, xn) ->
      assert (not (Atom.equal xp xn));
      let qp, qn = match v with
        | TyC.VNone -> TyS.create polarity, TyS.create (not polarity)
        | TyC.VPos qps -> merge_all env polarity qps, TyS.create (not polarity)
        | TyC.VNeg qns -> TyS.create polarity, merge_all env (not polarity) qns
        | TyC.VPosNeg (qps, qns) ->
          merge_all env polarity qps, merge_all env (not polarity) qns
      in
      assert (qp.TyS.polarity = polarity);
      assert (qn.TyS.polarity = not polarity);
      Atom.Map.add xn qn (Atom.Map.add xp qp am)
  ) Atom.Map.empty vs vas
  in
  t am

and resolve env polarity t =
  match t with
  | TyC.Tident (vs, n) ->
    (match Atom.Map.find n env.type_defs with
     | TTypeSynonym (typ, tyn) ->
       let vas = Atom.Map.find n env.type_variance in
       let q = do_instanciate env polarity
           (if polarity then typ else tyn) vs vas in
       resolve_all env polarity q.TyS.constructors
     | TBaseType _ -> TyCSet.singleton polarity t)
  | t -> TyCSet.singleton polarity t

and resolve_all env polarity ts =
  TyCSet.map_flatten (resolve env) polarity ts

and maybe_resolve env polarity1 polarity2 tc1 tc2 =
  if TyCSet.need_resolve polarity1 polarity2 tc1 tc2 then
    resolve_all env polarity1 tc1, resolve_all env polarity2 tc2
  else
    tc1, tc2

and cmerge env polarity tc1 tc2 =
  let tc1, tc2 = maybe_resolve env polarity polarity tc1 tc2 in
  TyCSet.merge polarity tc1 tc2

and scheme_merge env q1 q2 =
  let open TyS in
  assert (q1.polarity = q2.polarity);
  let qs = TySSet.diff q2.flow q1.flow in
  TySSet.iter (add_flow_edge q1) qs;
  q1.constructors <- cmerge env q1.polarity q1.constructors q2.constructors

and merge_all env polarity qs =
  let q = TyS.create polarity in
  TySSet.iter (scheme_merge env q) qs;
  q

module PTySSetMap = Map.Make(struct
    type t = bool * TySSet.t
    let compare (p1, qs1) (p2, qs2) =
      let u = compare p1 p2 in
      if u = 0 then
        TySSet.compare qs1 qs2
      else
        u
  end)

let rec simpl_tyss env st polarity qs =
  try PTySSetMap.find (polarity, qs) !st
  with Not_found ->
    let q = merge_all env polarity qs in
    let r = simpl_tys env st polarity q in
    st := PTySSetMap.add (polarity, qs) r !st;
    r

and simpl_tys env st polarity q =
  let q2 = TyS.create polarity in
  TySSet.iter (TyS.add_flow_edge q2) q.TyS.flow;
  q2.TyS.constructors <- List.map (simpl_tyc env st polarity) q.TyS.constructors;
  q2

and simpl_tyc env st polarity c =
  let open TyC in
  match c with
  | Tarrow (qs1, e, qs2) ->
    Tarrow (TySSet.singleton (simpl_tyss env st (not polarity) qs1),
            e,
            TySSet.singleton (simpl_tyss env st polarity qs2))
  | Tproduct qsl ->
    Tproduct (List.map (fun qs ->
        TySSet.singleton (simpl_tyss env st polarity qs)) qsl)
  | Tident (vs, n) -> Tident (List.map (simpl_var env st polarity) vs, n)

and simpl_var env st polarity v =
  let open TyC in
  match v with
  | VNone -> VNone
  | VPos qs -> VPos (TySSet.singleton (simpl_tyss env st polarity qs))
  | VNeg qs -> VNeg (TySSet.singleton (simpl_tyss env st (not polarity) qs))
  | VPosNeg (qps, qns) ->
    VPosNeg (TySSet.singleton (simpl_tyss env st polarity qps),
             TySSet.singleton (simpl_tyss env st (not polarity) qns))


let print_scheme env ff { hypotheses ; typ ; eff } =
  let st = ref PTySSetMap.empty in
  let typ = simpl_tys env st true typ in
  let hypotheses = Atom.Map.map
      (fun (q, _) -> simpl_tys env st false q) hypotheses in
  let l = typ :: (List.map snd (Atom.Map.bindings hypotheses)) in
  let st = T.prepare_printing l [eff] in
  if not (Atom.Map.is_empty hypotheses) then begin
    Format.fprintf ff "[@[<hov 2>";
    List.iteri (fun i (a, ty) ->
        if i > 0 then Format.fprintf ff ",@ ";
        Format.fprintf ff "%s : %a" (Atom.hint a) (T.print_tys st 0) ty
    ) (Atom.Map.bindings hypotheses);
    Format.fprintf ff "@]] "
  end;
  Format.fprintf ff "%a" (T.print_tys st 0) typ;
  Format.fprintf ff " !{%a}" (T.print_eff st 0 true) eff

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

exception BiUnificationFailure of TyC.t * TyC.t
exception EffBiUnificationFailure of TyE.t * TyE.t

let biunification_error t1 t2 =
  raise (BiUnificationFailure (t1, t2))

let eff_biunification_error e1 e2 =
  raise (EffBiUnificationFailure (e1, e2))

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

and merge_eff env name e1 e2 =
  let open TyE in
  assert (e1.polarity = e2.polarity);
  (match name with
   | None -> () | Some name -> extend name e1; extend name e2);
  let get e =
    match name with
    | None -> snd e.flows
    | Some name -> Atom.Map.find name (fst e.flows)
  in
  let es1, b1 = get e1 in
  let es2, b2 = get e2 in
  let es = TyESet.diff es2 es1 in
  TyESet.iter (add_flow_edge name e1) es;
  match name with
  | None ->
    if e1.polarity then
      assert (not b1 && not b2)
    else
      e1.flows <- (fst e1.flows, (fst (snd e1.flows), b1 || b2))
  | Some name -> e1.flows <- (Atom.Map.add name (fst (get e1), b1 || b2) (fst e1.flows), snd e1.flows)

and biunify_eff_excl ex env t ep em =
  TyE.common_domain ep em;
  assert (ep.TyE.polarity && not em.TyE.polarity);
  let (epf, epd) = ep.TyE.flows in
  let (emf, emd) = em.TyE.flows in
  Atom.Map.iter (fun name (es, _) -> if not (Atom.Set.mem name ex) then TyESet.iter (fun e -> merge_eff env (Some name) e ep) es) emf;
  Atom.Map.iter (fun name (es, _) -> if not (Atom.Set.mem name ex) then TyESet.iter (fun e -> merge_eff env (Some name) e em) es) epf;
  TyESet.iter (fun e -> merge_eff env None e ep) (fst emd);
  TyESet.iter (fun e -> merge_eff env None e em) (fst epd);
  assert (not (snd epd));
  Atom.Map.iter (fun name (_, bp) ->
      let (_, bm) = Atom.Map.find name emf in
      if bm && bp then
        eff_biunification_error ep em
    ) epf

and biunify_eff env = biunify_eff_excl Atom.Set.empty env

and biunify_tyc env t tp tm =
  let open TyC in
  match tp, tm with
  | Tident (vs1, n1), Tident (vs2, n2) ->
    if not (Atom.equal n1 n2) then
      biunification_error tp tm;
    assert (List.length vs1 = List.length vs2);
    List.iter2 (biunify_vs env t) vs1 vs2
  | Tarrow (tpa, effp, tpb), Tarrow (tma, effm, tmb) ->
    biunify_tyss env t tma tpa;
    biunify_tyss env t tpb tmb;
    biunify_eff env t effp effm
  | Tproduct l1, Tproduct l2 ->
    if List.length l1 = List.length l2 then
      List.iter2 (biunify_tyss env t) l1 l2
    else
      biunification_error tp tm
  | _, _ -> biunification_error tp tm

and biunify_vs env t vp vm =
  let open TyC in
  match vp, vm with
  | VNone, _ | _, VNone | VPos _, VNeg _ | VNeg _, VPos _ -> ()
  | VPos qp, VPos qm | VPos qp, VPosNeg (qm, _) | VPosNeg (qp, _), VPos qm ->
    biunify_tyss env t qp qm
  | VNeg qp, VNeg qm | VNeg qp, VPosNeg (_, qm) | VPosNeg (_, qp), VNeg qm ->
    biunify_tyss env t qm qp
  | VPosNeg (qp1, qp2), VPosNeg (qm1, qm2) ->
    biunify_tyss env t qp1 qm1;
    biunify_tyss env t qm2 qp2

let biunify_eff_excl excl env = biunify_eff_excl excl env (ref TySPSet.empty)
let biunify_eff env = biunify_eff env (ref TySPSet.empty)
let biunify env = biunify_tys env (ref TySPSet.empty)

let not_subtype_msg : _ format6 =
  "The type %a is not a subtype of the type %a@."
let not_subeffect_msg : _ format6 =
  "The effect %a is not a compatible with the effect %a@."

let check_biunify_msg (type a b) msg place env t1 t2 =
  if not !disable_type_checking then
    try biunify env t1 t2 with
    | BiUnificationFailure (ty1, ty2) ->
      let st = T.prepare_printing
          ([t1; t2] @
           TySSet.(elements (union (T.tyc_succ ty1) (T.tyc_succ ty2)))) []
      in
      error place (msg ^^ "@.%t")
        (T.print_tys st 0) t1 (T.print_tys st 0) t2
        (fun ff -> Format.fprintf ff not_subtype_msg (T.print_tyc st 0 true) ty1 (T.print_tyc st 0 false) ty2)
    | EffBiUnificationFailure (e1, e2) ->
      let st = T.prepare_printing [t1; t2] [e1; e2] in
      error place (msg ^^ "@.%t")
        (T.print_tys st 0) t1 (T.print_tys st 0) t2
        (fun ff -> Format.fprintf ff not_subeffect_msg (T.print_eff st 0 true) e1 (T.print_eff st 0 false) e2)

let check_biunify =
  check_biunify_msg "This expression has type %a but was expected of type %a@."

let check_biunify_eff_excl_msg msg excl place env t1 t2 =
  if not !disable_type_checking then
    try biunify_eff_excl excl env t1 t2 with
    | EffBiUnificationFailure (e1, e2) ->
      let st = T.prepare_printing [] [t1; t2; e1; e2] in
      error place (msg ^^ "@.%t")
        (T.print_eff st 0 true) t1 (T.print_eff st 0 false) t2
        (fun ff -> Format.fprintf ff not_subeffect_msg (T.print_eff st 0 true) e1 (T.print_eff st 0 false) e2)

let check_biunify_eff_excl =
  check_biunify_eff_excl_msg "This expression has effect %a but was expected to have effect %a"

let check_biunify_eff = check_biunify_eff_excl Atom.Set.empty

let add_bound id a env =
  { env with bindings = Smap.add id (BInfer, a) env.bindings }

let add id env =
  let a = Atom.fresh id in
  add_bound id a env, a

let empty_eff polarity =
  let w = TyE.create polarity in
  w.TyE.flows <- (Atom.Map.empty, (TyESet.empty, not polarity));
  w

let add_gen id scheme env =
  let a = Atom.fresh id in
  let scheme = { scheme with eff = empty_eff true } in
  let nenv = { env with bindings = Smap.add id (BScheme scheme, a) env.bindings } in
  (nenv, a)

let copy_scheme { hypotheses ; typ ; eff } =
  let l = typ :: (List.map (fun (_, (st, _)) -> st)
                           (Atom.Map.bindings hypotheses)) in
  let st = T.prepare_copy l [eff] in
  {
    hypotheses = Atom.Map.map
        (fun (ty, place) -> (T.copy st ty, place)) hypotheses ;
    typ = T.copy st typ ;
    eff = T.eff_copy st eff ;
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
      eff = empty_eff true ;
    } in
    sc, a

let unify_hyp_many env l =
  List.fold_left (unify_hyp env) Atom.Map.empty l

let create_var_pair = function
  | ANone -> TyC.VNone, TyC.VNone
  | APos _ ->
    let qp, qn = TyS.create_flow_pair () in
    TyC.VPos (TySSet.singleton qp), TyC.VPos (TySSet.singleton qn)
  | ANeg _ ->
    let qp, qn = TyS.create_flow_pair () in
    TyC.VNeg (TySSet.singleton qn), TyC.VNeg (TySSet.singleton qp)
  | APosNeg _ ->
    let qp1, qn1 = TyS.create_flow_pair () in
    let qp2, qn2 = TyS.create_flow_pair () in
    TyC.VPosNeg (TySSet.singleton qp1, TySSet.singleton qn2),
    TyC.VPosNeg (TySSet.singleton qn1, TySSet.singleton qp2)

let create_var_pairs l =
  List.split (List.map create_var_pair l)

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
    let w = T.arrow_option true src sc.eff sc.typ in
    let nsc = {
      hypotheses = nh ;
      typ = w ;
      eff = empty_eff true ;
    } in
    nsc, T.Lam (T.NoSelf, x, t)
  | S.App (t1, t2) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let (wp, wn) = TyS.create_flow_pair () in
    let (ep, en) = TyE.create_flow_pair () in
    let w = T.arrow false sc2.typ en wn in
    let nh = unify_hyp env sc1.hypotheses sc2.hypotheses in
    check_biunify t1.S.place env sc1.typ w;
    check_biunify_eff t1.S.place env sc1.eff en;
    check_biunify_eff t2.S.place env sc2.eff en;
    let nsc = {
      hypotheses = nh ;
      typ = wp ;
      eff = ep ;
    } in
    nsc, T.App (nt1, nt2)
  | S.Lit i ->
    let w = T.ident true builtin_int_id [] in
    let sc = {
      hypotheses = Atom.Map.empty ;
      typ = w ;
      eff = empty_eff true ;
    } in
    sc, T.Lit i
  | S.BinOp (t1, op, t2) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let nh = unify_hyp env sc1.hypotheses sc2.hypotheses in
    let w1 = T.ident true builtin_int_id [] in
    let w2 = T.ident false builtin_int_id [] in
    let (ep, en) = TyE.create_flow_pair () in
    check_biunify t1.S.place env sc1.typ w2;
    check_biunify t2.S.place env sc2.typ w2;
    check_biunify_eff t1.S.place env sc1.eff en;
    check_biunify_eff t2.S.place env sc2.eff en;
    let sc = {
      hypotheses = nh ;
      typ = w1 ;
      eff = ep ;
    } in
    sc, T.BinOp (nt1, op, nt2)
  | S.Print t ->
    let sc, nt = cook_term env t in
    let w1 = T.ident true builtin_int_id [] in
    let w2 = T.ident false builtin_int_id [] in
    let (ep, en) = TyE.create_flow_pair () in
    let e = TyE.create true in
    e.TyE.flows <- (Atom.Map.singleton builtin_io_id (TyESet.empty, true), (TyESet.empty, false));
    check_biunify t.S.place env sc.typ w2;
    check_biunify_eff t.S.place env sc.eff en;
    check_biunify_eff t.S.place env e en;
    { sc with eff = ep ; typ = w1 }, T.Print nt
  | S.Let (recursive, x, t1, t2) ->
    let nenv, x, sc1, nt1 = cook_let env recursive x t1 in
    let sc2, nt2 = cook_term nenv t2 in
    let (ep, en) = TyE.create_flow_pair () in
    check_biunify_eff t1.S.place env sc1.eff en;
    check_biunify_eff t2.S.place env sc2.eff en;
    let nh = unify_hyp env sc1.hypotheses sc2.hypotheses in
    let nsc = {
      hypotheses = nh ;
      typ = sc2.typ ;
      eff = ep ;
    } in
    nsc, T.Let (x, nt1, nt2)
  | S.IfZero (t1, t2, t3) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let sc3, nt3 = cook_term env t3 in
    let nh = unify_hyp env sc1.hypotheses
        (unify_hyp env sc2.hypotheses sc3.hypotheses) in
    let (wp, wn) = TyS.create_flow_pair () in
    let (ep, en) = TyE.create_flow_pair () in
    let w = T.ident false builtin_int_id [] in
    check_biunify t1.S.place env sc1.typ w;
    check_biunify t2.S.place env sc2.typ wn;
    check_biunify t3.S.place env sc3.typ wn;
    check_biunify_eff t1.S.place env sc1.eff en;
    check_biunify_eff t2.S.place env sc2.eff en;
    check_biunify_eff t3.S.place env sc3.eff en;
    let nsc = {
      hypotheses = nh ;
      typ = wp ;
      eff = ep ;
    } in
    nsc, T.IfZero (nt1, nt2, nt3)
  | S.Tuple l ->
    let l = List.map (cook_term env) l in
    let nh = unify_hyp_many env (List.map (fun (sc, _) -> sc.hypotheses) l) in
    let w = T.product true (List.map (fun (sc, _) -> sc.typ) l) in
    let (ep, en) = TyE.create_flow_pair () in
    List.iter (fun (sc, _) -> check_biunify_eff place env sc.eff en) l;
    let nsc = {
      hypotheses = nh ;
      typ = w ;
      eff = ep ;
    } in
    nsc, (T.Tuple (List.map snd l))
  | S.Constructor (x, t) ->
    let catom =
      try Smap.find x env.constructor_bindings
      with Not_found -> error place "Unbound constructor: %s" x
    in
    let tname, cargs, ctag, is_effect = Atom.Map.find catom env.constructor_defs in
    let targs =
      if is_effect then
        []
      else
        Atom.Map.find tname env.type_variance
    in
    let tap, tan = create_var_pairs targs in
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
    let (ep, en) = TyE.create_flow_pair () in
    let nh = unify_hyp_many env
        (List.map (fun (_, (sc, _)) -> sc.hypotheses) args) in
    List.iter2 (fun (place, (sc, _)) (_, enty) ->
        check_biunify place env sc.typ (do_instanciate env false enty tan targs);
        check_biunify_eff place env sc.eff en;
    ) args cargs;
    let nt =
      if is_effect then begin
        let (_, (npt, _), _) = Atom.Map.find tname env.effect_defs in
        let e = TyE.create true in
        e.TyE.flows <- (Atom.Map.singleton tname (TyESet.empty, true), (TyESet.empty, false));
        check_biunify_eff place env e en;
        do_instanciate env true npt tap targs
      end else
        T.ident true tname tap
    in
    let nsc = {
      hypotheses = nh ;
      typ = nt ;
      eff = ep ;
    } in
    nsc, T.Constructor ((catom, ctag, is_effect),
                        List.map (fun (_, (_, t)) -> t) args)
  | S.Match (t, l) ->
    let sc, nt = cook_term env t in
    let rtyp, rtyn = TyS.create_flow_pair () in
    let ep, en = TyE.create_flow_pair () in
    let erp, ern = TyE.create_flow_pair () in
    check_biunify_eff t.S.place env sc.eff en;
    let matched_effects = ref Atom.Set.empty in
    let nl = List.map (fun (p, t1) ->
      let np, dv, ef = cook_pattern_or_effect env sc.typ rtyp erp p in
      matched_effects := Atom.Set.union !matched_effects ef;
      let nenv = Smap.fold (fun x (a, t) env -> add_bound x a env) dv env in
      let sc1, nt1 = cook_term nenv t1 in
      check_biunify t1.S.place env sc1.typ rtyn;
      check_biunify_eff t1.S.place env sc1.eff ern;
      let nh = Smap.fold (fun _ (a, t) h ->
          try
            let ty, place = Atom.Map.find a h in
            check_biunify place env t ty;
            Atom.Map.remove a h
          with Not_found -> h
      ) dv sc1.hypotheses in
      (nh, (np, nt1))
    ) l in
    Atom.Set.iter (fun name -> TyE.extend name ep) !matched_effects;
    Atom.Set.iter (fun name -> TyE.extend name ern) !matched_effects;
    check_biunify_eff_excl !matched_effects place env ep ern;
    let nsc = {
      hypotheses = List.fold_left
          (fun h1 (h2, _) -> unify_hyp env h1 h2) sc.hypotheses nl ;
      typ = rtyp ;
      eff = erp ;
    } in
    nsc, T.Match (nt, List.map snd nl)

and cook_pattern_or_effect env ty rty ep = function
  | S.Pattern p ->
    let p, dv = cook_pattern env Smap.empty ty p in
    T.Pattern p, dv, Atom.Set.empty
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
        let np, dv = cook_pattern env Smap.empty (do_instanciate env true ty1p [] []) p in
        if Smap.mem k dv then
          error p.S.place "The variable %s is already bound in this matching" k;
        T.PConstructor ((catom, ctag, true), [np]), dv
      | None, Some _ ->
        error place "The effect constructor %s expects 1 argument, but is applied here to 0 arguments" c
      | Some _, None ->
        error place "The effect constructor %s expects 0 arguments, but is applied here to 1 argument" c
    in
    (* For now, assure this means the effect is matched (no exhausitivty checking). *)
    let kty = T.arrow true (do_instanciate env false ty2n [] []) ep rty in
    let kv = Atom.fresh k in
      T.Effect (np, kv), (Smap.add k (kv, kty) dv), Atom.Set.singleton ename

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
        let wp, wn = TyS.create_flow_pair () in
        check_biunify place env ty1 wn;
        check_biunify place env ty2 wn;
        Some (a1, wp)
      | _ -> error place "Variable %s must appear on both sides of this | pattern" x
    ) dv1 dv2 in
    np, dv
  | S.PTuple l ->
    let ws = List.map (fun _ -> TyS.create_flow_pair ()) l in
    check_biunify_msg "A pattern was expected which matches values of type %a but this pattern matches values of type %a" place env ty (T.product false (List.map snd ws));
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
    let targs = Atom.Map.find tname env.type_variance in
    let tap, tan = create_var_pairs targs in
    check_biunify_msg "A pattern was expected which matches values of type %a but this pattern matches values of type %a" place env ty (T.ident false tname tan);
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
    let nl = List.map2 (cook_pattern env mapped_vars)
        (List.map (fun (ap, _) -> do_instanciate env true ap tap targs) cargs)
        args
    in
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
      let w = T.arrow_option true src sc.eff sc.typ in
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
        eff = empty_eff true ;
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
  | S.TVariable x ->
    let np, nn =
      try
        Smap.find x env.type_variables
      with Not_found -> error place "Unbound type variable: '%s" x
    in
    let n = if polarity then np else nn in
    fun inst ->
      let q = Atom.Map.find n inst in
      assert (q.TyS.polarity = polarity);
      q
  | S.TConstructor (l, x) -> begin
    match Smap.find x env.type_bindings with
    | n ->
      let va = Atom.Map.find n env.type_variance in
      if List.length va <> List.length l then
        error place "The type constructor %s expects %d arguments but was given %d arguments" x (List.length va) (List.length l);
      let nl = List.map2 (cook_var env polarity) va l in
      fun inst ->
        T.ident polarity n (List.map (fun t -> t inst) nl)
    | exception Not_found -> error place "Unbound type: %s" x
    end
  | S.TArrow (t1, t2) -> (* TODO *)
    let t1 = cook_type env (not polarity) t1 in
    let t2 = cook_type env polarity t2 in
    fun inst ->
      T.arrow polarity (t1 inst) (empty_eff polarity) (t2 inst)
  | S.TTuple l ->
    let l = List.map (cook_type env polarity) l in
    fun inst ->
      T.product polarity (List.map (fun t -> t inst) l)

and cook_var env polarity va t =
  match va with
  | ANone -> fun inst -> TyC.VNone
  | APos _ ->
    let t = cook_type env polarity t in
    fun inst -> TyC.VPos (TySSet.singleton (t inst))
  | ANeg _ ->
    let t = cook_type env (not polarity) t in
    fun inst -> TyC.VNeg (TySSet.singleton (t inst))
  | APosNeg _ ->
    let tp = cook_type env polarity t in
    let tn = cook_type env (not polarity) t in
    fun inst -> TyC.VPosNeg (TySSet.singleton (tp inst), TySSet.singleton (tn inst))

let rec cook_program env = function
  | { S.value = S.DTerm t ; S.place } :: p ->
    let a = Atom.fresh "_" in
    let sc, nt = cook_term env t in
    assert (Atom.Map.is_empty sc.hypotheses);
    let e = TyE.create false in
    e.TyE.flows <- (Atom.Map.singleton builtin_io_id (TyESet.empty, false),
                (TyESet.empty, true));
    check_biunify_eff place env sc.eff e;
    T.Let (a, nt, cook_program env p)
  | { S.value = S.DLet (recursive, x, t) ; S.place } :: p ->
    let env, nx, sc, nt = cook_let env recursive x t in
    assert (Atom.Map.is_empty sc.hypotheses);
    Format.eprintf "val %s : @[<hv>%a@]@." x (print_scheme env) sc;
    let e = TyE.create false in
    e.TyE.flows <- (Atom.Map.singleton builtin_io_id (TyESet.empty, false),
                (TyESet.empty, true));
    check_biunify_eff place env sc.eff e;
    T.Let (nx, nt, cook_program env p)
  | { S.value = S.DTypeSynonym ((args, x), t) ; _ } :: p ->
    let n = Atom.fresh x in
    let vars = List.map (fun x -> (Atom.fresh x, Atom.fresh x)) args in
    let vas = List.map (fun (x, y) -> APosNeg (x, y)) vars in
    let vamp = List.fold_left2 (fun vam x v -> Smap.add x v vam) env.type_variables args vars in
    let vamn = List.fold_left2 (fun vam x (u, v) -> Smap.add x (v, u) vam) env.type_variables args vars in
    let env1p = { env with type_variables = vamp } in
    let env1n = { env with type_variables = vamn } in
    let nenv = { env with
      type_bindings = Smap.add x n env.type_bindings ;
      type_defs = Atom.Map.add n
          (TTypeSynonym (cook_type env1p true t, cook_type env1n false t))
          env.type_defs ;
      type_variance = Atom.Map.add n vas env.type_variance ;
    } in
    cook_program nenv p
  | { S.value = S.DNewType ((args, x), l) ; _ } :: p ->
    let n = Atom.fresh x in
    let vars = List.map (fun x -> (Atom.fresh x, Atom.fresh x)) args in
    let vas = List.map (fun (x, y) -> APosNeg (x, y)) vars in
    let vamp = List.fold_left2 (fun vam x v -> Smap.add x v vam) env.type_variables args vars in
    let vamn = List.fold_left2 (fun vam x (u, v) -> Smap.add x (v, u) vam) env.type_variables args vars in
    let env1 = { env with
      type_bindings = Smap.add x n env.type_bindings ;
      type_variance = Atom.Map.add n vas env.type_variance ;
    } in
    let env1p = { env1 with type_variables = vamp } in
    let env1n = { env1 with type_variables = vamn } in
    let constructors = List.map
        (fun { S.value = (name, r) ; _ } ->
           (name, Atom.fresh name,
            List.map (fun t ->
                cook_type env1p true t, cook_type env1n false t) r)
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
