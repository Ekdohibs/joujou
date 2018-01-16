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

module ISet = Set.Make(struct type t = int let compare = compare end)
type aut_head =
  | HArrow | HIdent of Atom.atom | HTuple of int | HVar of int
type aut_label =
  | LArrowsrc | LArrowdst
  | LTuple of int * int (* arity * pos *)
module AH = struct type t = aut_head let compare = compare end
module AHSet = Set.Make(AH)
module AL = struct type t = aut_label let compare = compare end
module ALMap = Map.Make(AL)
type aut = {
  data : (int, (bool * AHSet.t * ISet.t ALMap.t)) Hashtbl.t ;
  mutable num_states : int ;
}

let from_bindings l =
  List.fold_left (fun m (a, b) -> ALMap.add a b m) ALMap.empty l

let ( <|> ) a b =
  let rec aux a b r =
    if b <= a then r else aux a (b - 1) ((b - 1) :: r)
  in aux a b []

let builtin_int_id = Atom.fresh "int"
let builtin_int = T.Tident builtin_int_id

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

type scheme = {
  (* First place where the variable was used, for error reporting. *)
  hypotheses : (Ty.t * place) Atom.Map.t ;
  typ : Ty.t ;
}

type scheme_aut = {
  sa_aut : aut ;
  mutable sa_flow : (int * int) list ;
  mutable sa_hypotheses : (int * place) Atom.Map.t ;
  mutable sa_typ : int ;
}

let aut_copy aut =
  {
    num_states = aut.num_states ;
    data = Hashtbl.copy aut.data ;
  }

let sa_copy sc =
  {
    sa_aut = aut_copy sc.sa_aut ;
    sa_flow = sc.sa_flow ;
    sa_hypotheses = sc.sa_hypotheses ;
    sa_typ = sc.sa_typ ;
  }

let check_polarity sc =
  Hashtbl.iter (fun _ (polarity, _, nxt) ->
    ALMap.iter (fun label s ->
      ISet.iter (fun t ->
        let p2, _, _ = Hashtbl.find sc.sa_aut.data t in
        assert ((polarity = p2) = (label <> LArrowsrc))) s
    ) nxt
  ) sc.sa_aut.data

let flow_get_n polarity s l =
  List.fold_left (fun s1 (a, b) ->
      let u, v = if polarity then a, b else b, a in
      if ISet.mem v s then ISet.add u s1 else s1) ISet.empty l

let of_scheme_aut sc =
  let open T in
  let seen = Hashtbl.create 17 in
  let jm_all polarity =
    if polarity then List.fold_left tjoin Tbot
    else List.fold_left tmeet Ttop
  in
  let flow_vars = Hashtbl.create 17 in
  let rec decompose_flow fl =
    let best = ref (ISet.empty, ISet.empty) in
    let best_v = ref 0 in
    let neg = ISet.of_list (List.map fst fl) in
    let pos = ISet.of_list (List.map snd fl) in
    ISet.iter (fun q ->
        let qs1 = flow_get_n false (ISet.singleton q) fl in
        let qs2 = flow_get_n true qs1 fl in
        let v = (ISet.cardinal qs1) * (ISet.cardinal qs2) in
        if v > !best_v then begin
          best_v := v;
          best := (qs2, qs1)
        end) neg;
    ISet.iter (fun q ->
        let qs1 = flow_get_n true (ISet.singleton q) fl in
        let qs2 = flow_get_n false qs1 fl in
        let v = (ISet.cardinal qs1) * (ISet.cardinal qs2) in
        if v > !best_v then begin
          best_v := v;
          best := (qs1, qs2)
        end) pos;
    if !best_v > 0 then begin
      let qs1, qs2 = !best in
      let v = TV.create () in
      ISet.iter (fun q ->
        Hashtbl.replace flow_vars q
          (TVSet.add (TV.of_typevar v) (try Hashtbl.find flow_vars q with Not_found -> TVSet.empty))
      ) (ISet.union qs1 qs2);
      let fl = List.filter (fun (q1, q2) -> not (ISet.mem q1 qs1 && ISet.mem q2 qs2)) fl in
      decompose_flow fl
    end
  in
  decompose_flow sc.sa_flow;
  let rec walk q =
    let polarity, head, nxt = Hashtbl.find sc.sa_aut.data q in
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
          | HVar id -> assert false
          | HIdent n -> Tident n
          | HArrow ->
            let src = List.map walk
                (ISet.elements (try ALMap.find LArrowsrc nxt with Not_found -> ISet.empty)) in
            let dst = List.map walk
                (ISet.elements (try ALMap.find LArrowdst nxt with Not_found -> ISet.empty)) in
            Tarrow (jm_all (not polarity) src, Rempty, jm_all polarity dst)
          | HTuple arity ->
            let l = List.map (fun i ->
                jm_all polarity (List.map walk
                  (ISet.elements (try ALMap.find (LTuple (arity, i)) nxt with Not_found -> ISet.empty)))
            ) (0 <|> arity) in
            Tproduct l
        ) head in
      let nty = nty @
        List.map (fun tv -> Tvar (TV.to_typevar tv))
          (TVSet.elements (try Hashtbl.find flow_vars q with Not_found -> TVSet.empty)) in
      let ty = jm_all polarity nty in
      let r = match Hashtbl.find seen q with
        | None -> ty
        | Some tv -> Trec(tv, ty)
      in
      Hashtbl.remove seen q;
      r
    end
  in
  {
    hypotheses =
      Atom.Map.map (fun (q, place) -> (walk q, place)) sc.sa_hypotheses ;
    typ = walk sc.sa_typ ;
  }

let fvars_scheme { hypotheses ; typ } =
  Atom.Map.fold
    (fun _ (ty, _) s -> TVSet.union s (Ty.fvars ty)) hypotheses (Ty.fvars typ)

let print_vars_scheme { hypotheses ; typ } =
  Atom.Map.fold
    (fun _ (ty, _) s -> TVSet.union s (Ty.print_vars ty))
    hypotheses (Ty.print_vars typ)

let print_scheme ff { hypotheses ; typ } =
  let fv = print_vars_scheme { hypotheses ; typ } in
  let pnames = TV.get_print_names fv fv in
  Format.fprintf ff "[@[<hov 2>";
  List.iteri (fun i (a, (ty, _)) ->
      if i > 0 then Format.fprintf ff ",@ ";
      Format.fprintf ff "%s : %a" (Atom.hint a) (Ty.print pnames 0) ty
    ) (Atom.Map.bindings hypotheses);
  Format.fprintf ff "@]] %a" (Ty.print pnames 0) typ

let scheme_update update_typ sc1 sc2 =
  (* check_polarity sc1;
     check_polarity sc2; *)
  let n = sc1.sa_aut.num_states in
  let flow = List.map (fun (x, y) -> (x + n, y + n)) sc2.sa_flow @ sc1.sa_flow in
  sc1.sa_flow <- flow;
  sc1.sa_aut.num_states <- n + sc2.sa_aut.num_states;
  Hashtbl.iter (fun q (polarity, head, nxt) ->
    Hashtbl.add sc1.sa_aut.data (q + n)
      (polarity, head, ALMap.map (fun s -> ISet.map (fun q1 -> q1 + n) s) nxt)
  ) sc2.sa_aut.data;
  sc1.sa_hypotheses <- Atom.Map.merge (fun _ h1 h2 ->
    match h1, h2 with
    | None, None -> None
    | Some (q1, place), None -> Some (q1, place)
    | None, Some (q2, place) -> Some (q2 + n, place)
    | Some (q1, place), Some (q2, _) ->
      let w = sc1.sa_aut.num_states in
      sc1.sa_aut.num_states <- w + 1;
      Hashtbl.add sc1.sa_aut.data w
        (merge_st (Hashtbl.find sc1.sa_aut.data q1)
           (Hashtbl.find sc1.sa_aut.data (q2 + n)));
      let fp = flow_get_n false (ISet.of_list [q1; q2 + n]) sc1.sa_flow in
      ISet.iter (fun q -> sc1.sa_flow <- (w, q) :: sc1.sa_flow) fp;
      Some (w, place)
    ) sc1.sa_hypotheses sc2.sa_hypotheses;
  if update_typ then begin
    let w = sc1.sa_aut.num_states in
    sc1.sa_aut.num_states <- w + 1;
    Hashtbl.add sc1.sa_aut.data w
      (merge_st (Hashtbl.find sc1.sa_aut.data sc1.sa_typ)
         (Hashtbl.find sc1.sa_aut.data (sc2.sa_typ + n)));
    sc1.sa_typ <- w
  end
  (* check_polarity sc1 *)

let scheme_merge sc q1 q2 =
  check_polarity sc;
  Hashtbl.replace sc.sa_aut.data q1
    (merge_st (Hashtbl.find sc.sa_aut.data q1) (Hashtbl.find sc.sa_aut.data q2));
  let polarity, _, _ = Hashtbl.find sc.sa_aut.data q1 in
  let s1 = flow_get_n polarity (ISet.singleton q1) sc.sa_flow in
  let s2 = flow_get_n polarity (ISet.singleton q2) sc.sa_flow in
  let l = ISet.(elements (diff s2 s1)) in
  let l = List.map (fun x -> if polarity then (x, q1) else (q1, x)) l in
  sc.sa_flow <- l @ sc.sa_flow;
  check_polarity sc;

exception Compatibility_error
let check_compatible head1 head2 =
  AHSet.iter (fun h1 -> AHSet.iter (fun h2 ->
    match h1, h2 with
    | HVar _, _ | _, HVar _ -> assert false
    | HArrow, HArrow -> ()
    | HTuple n1, HTuple n2 when n1 = n2 -> ()
    | HIdent name1, HIdent name2 when Atom.equal name1 name2 -> ()
    | _ -> raise Compatibility_error
  ) head1) head2

let rec biunify t sc qp qm =
  if not (Hashtbl.mem t (qp, qm)) then begin
    Hashtbl.add t (qp, qm) ();
    let (polarity1, head1, nxt1) = Hashtbl.find sc.sa_aut.data qp in
    let (polarity2, head2, nxt2) = Hashtbl.find sc.sa_aut.data qm in
    assert (polarity1 && not polarity2);
    check_compatible head1 head2;
    ISet.iter (fun q -> scheme_merge sc q qp)
      (flow_get_n false (ISet.singleton qm) sc.sa_flow);
    ISet.iter (fun q -> scheme_merge sc q qm)
      (flow_get_n true (ISet.singleton qp) sc.sa_flow);
    ALMap.iter (fun label q1s ->
      let q2s = try ALMap.find label nxt2 with Not_found -> ISet.empty in
      ISet.iter (fun q1 -> ISet.iter (fun q2 ->
          if label = LArrowsrc then biunify t sc q2 q1 else biunify t sc q1 q2
      ) q2s) q1s
    ) nxt1
  end

let biunify sc = biunify (Hashtbl.create 17) sc

type binding =
  | BScheme of scheme_aut
  | BInfer

type typedef =
  | TBaseType of Atom.atom
  | TTypeSynonym of Ty.t

module Smap = Map.Make(String)
type env = {
  bindings : (binding * Atom.atom) Smap.t ;
  (*  fvars : TVSet.t ; *)
  type_bindings : Atom.atom Smap.t ;
  type_defs : typedef Atom.Map.t ;
  constructor_bindings : Atom.atom Smap.t ;
  constructor_defs : (Atom.atom * Ty.t list * int * bool) Atom.Map.t ;
  effect_bindings : Atom.atom Smap. t;
  effect_defs : (Ty.t option * Ty.t * int) Atom.Map.t ;
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

exception UnificationFailure of Ty.t * Ty.t

let unification_error t1 t2 =
  raise (UnificationFailure (Ty.canon t1, Ty.canon t2))

let rec occur var t =
  let open T in
  match (Ty.head t) with
  | Tident _ | Tbot | Ttop -> false
  | Tarrow (ta, r, tb) -> occur var ta || occur var tb
  | Tproduct l -> List.exists (occur var) l
  | Tvar tv -> TV.equal (TV.of_typevar tv) var
  | Tjoin (t1, t2) | Tmeet (t1, t2) -> occur var t1 || occur var t2
  | Trec (_, t1) -> occur var t1

let rec resolve env t =
  let open T in
  match (Ty.head t) with
  | Tident n ->
    (match Atom.Map.find n env.type_defs with
     | TTypeSynonym t -> resolve env t
     | TBaseType n -> Tident n)
  | t -> t

(*
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
    TV.bind v T.Reffect (name, T.Rvar nv);
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
  | None, Some v | Some v, None -> TV.bind v T.Rempty
  | Some v1, Some v2 ->
    if TV.eq v1 v2 then ()
    else TV.bind v1 (T.Rvar v2)
*)

let rec unify env t1 t2 =
  let open T in
  match (resolve env t1), (resolve env t2) with
  | Tident n1, Tident n2 ->
    if not (Atom.equal n1 n2) then
      unification_error t1 t2
  | Tarrow (t1a, r1, t1b), Tarrow (t2a, r2, t2b) ->
    unify env t1a t2a; unify env t1b t2b (*; unify_row r1 r2 *)
  | Tproduct l1, Tproduct l2 ->
    if List.length l1 <> List.length l2 then
      unification_error t1 t2
    else
      List.iter2 (unify env) l1 l2
  | Tvar tv1, Tvar tv2 ->
    if not (TV.eq tv1 tv2) then
      TV.bind tv1 t2
  | Tvar tv, t | t, Tvar tv ->
    if occur (TV.of_typevar tv) t then
      unification_error t1 t2
    else
      TV.bind tv t
  | _ -> unification_error t1 t2

let check_unify_msg msg place env t1 t2 =
  if not !disable_type_checking then
    try unify env t1 t2 with
    | UnificationFailure (ty1, ty2) ->
      error place msg (T.show_typ (Ty.canon t1)) (T.show_typ (Ty.canon t2)) (T.show_typ (Ty.canon ty1)) (T.show_typ (Ty.canon ty2))

let check_unify = check_unify_msg "This expression has type %s but was expected of type %s\nThe type %s is incompatible with the type %s"

(*
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
*)

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

let refresh_scheme { hypotheses ; typ } =
  let fvars = fvars_scheme { hypotheses ; typ } in
  let m = TVSet.fold (fun v m -> T.TVMap.add v (TV.copy v) m) fvars T.TVMap.empty in
  {
    hypotheses = Atom.Map.map
        (fun (ty, place) -> (Ty.refresh_rec m ty, place)) hypotheses ;
    typ = Ty.refresh_rec m typ ;
  }

let unify_hyp env hp1 hp2 =
  Atom.Map.merge (fun _ ty1 ty2 ->
      match ty1, ty2 with
      | None, None -> None
      | None, Some ty | Some ty, None -> Some ty
      | Some (ty1, place1), Some (ty2, place2) ->
        check_unify place2 env ty1 ty2;
        Some (ty1, place1)
  ) hp1 hp2

let find place id env =
  let (sc, a) = Smap.find id env.bindings in
  match sc with
  | BScheme sc -> sa_copy sc, a
  | BInfer ->
    let sc = {
      sa_aut = { num_states = 2 ; data = Hashtbl.create 2 } ;
      sa_hypotheses = Atom.Map.singleton a (0, place) ;
      sa_typ = 1 ;
      sa_flow = [(0, 1)] ;
    } in
    Hashtbl.add sc.sa_aut.data 0 (false, AHSet.empty, ALMap.empty);
    Hashtbl.add sc.sa_aut.data 1 (true, AHSet.empty, ALMap.empty);
    sc, a

let new_state aut =
  let w = aut.num_states in
  aut.num_states <- w + 1;
  w

let scheme_join_many l =
  let sc = {
    sa_aut = { num_states = 0 ; data = Hashtbl.create 0 } ;
    sa_hypotheses = Atom.Map.empty ;
    sa_typ = 0 ;
    sa_flow = [] ;
  } in
  let l = List.map (fun sc1 ->
      let n = sc.sa_aut.num_states in
      scheme_update false sc sc1;
      sc1.sa_typ + n) l in
  sc, l

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
    let w = new_state sc.sa_aut in
    let nxt =
      try
        let ty, _ = Atom.Map.find x sc.sa_hypotheses in
        sc.sa_hypotheses <- Atom.Map.remove x sc.sa_hypotheses;
        from_bindings [LArrowsrc, ISet.singleton ty ;
                       LArrowdst, ISet.singleton sc.sa_typ]
      with Not_found ->
        from_bindings [LArrowdst, ISet.singleton sc.sa_typ]
    in
    sc.sa_typ <- w;
    Hashtbl.add sc.sa_aut.data w (true, AHSet.singleton HArrow, nxt);
    sc, T.Lam (T.NoSelf, x, t)
  | S.App (t1, t2) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let ty1, ty2 = sc1.sa_typ, sc2.sa_typ + sc1.sa_aut.num_states in
    scheme_update false sc1 sc2;
    let w1 = new_state sc1.sa_aut in
    Hashtbl.add sc1.sa_aut.data w1 (true, AHSet.empty, ALMap.empty);
    let w2 = new_state sc1.sa_aut in
    Hashtbl.add sc1.sa_aut.data w2 (false, AHSet.empty, ALMap.empty);
    sc1.sa_flow <- (w2, w1) :: sc1.sa_flow;
    let w3 = new_state sc1.sa_aut in
    Hashtbl.add sc1.sa_aut.data w3
      (false, AHSet.singleton HArrow,
       from_bindings [LArrowsrc, ISet.singleton ty2 ;
                      LArrowdst, ISet.singleton w2]);
    sc1.sa_typ <- w1;
    biunify sc1 ty1 w3;
    sc1, T.App (nt1, nt2)
  | S.Lit i ->
    let sc = {
      sa_aut = { num_states = 1 ; data = Hashtbl.create 1 } ;
      sa_hypotheses = Atom.Map.empty ;
      sa_typ = 0 ;
      sa_flow = [] ;
    } in
    Hashtbl.add sc.sa_aut.data 0
      (true, AHSet.singleton (HIdent builtin_int_id), ALMap.empty);
    sc, T.Lit i
  | S.BinOp (t1, op, t2) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let ty1, ty2 = sc1.sa_typ, sc2.sa_typ + sc1.sa_aut.num_states in
    scheme_update false sc1 sc2;
    let w1 = new_state sc1.sa_aut in
    Hashtbl.add sc1.sa_aut.data w1
      (true, AHSet.singleton (HIdent builtin_int_id), ALMap.empty);
    let w2 = new_state sc1.sa_aut in
    Hashtbl.add sc1.sa_aut.data w2
      (false, AHSet.singleton (HIdent builtin_int_id), ALMap.empty);
    sc1.sa_typ <- w1;
    biunify sc1 ty1 w2;
    biunify sc1 ty2 w2;
    sc1, T.BinOp (nt1, op, nt2)
  | S.Print t ->
    let sc, nt = cook_term env t in
    let w1 = new_state sc.sa_aut in
    Hashtbl.add sc.sa_aut.data w1
      (false, AHSet.singleton (HIdent builtin_int_id), ALMap.empty);
    biunify sc sc.sa_typ w1;
    (* TODO: print produces io effect *)
    sc, T.Print nt
  | S.Let (recursive, x, t1, t2) ->
    let nenv, x, sc1, nt1 = cook_let env recursive x t1 in
    (*    Format.eprintf "val %s : @[<hv>%a@]@." (Atom.hint x) print_scheme sc1; *)
    let sc1 = sa_copy sc1 in
    let sc2, nt2 = cook_term nenv t2 in
    let ty2 = sc2.sa_typ + sc1.sa_aut.num_states in
    scheme_update false sc1 sc2;
    sc1.sa_typ <- ty2;
    sc1, T.Let (x, nt1, nt2)
  | S.IfZero (t1, t2, t3) ->
    let sc1, nt1 = cook_term env t1 in
    let sc2, nt2 = cook_term env t2 in
    let sc3, nt3 = cook_term env t3 in
    let ty1 = sc1.sa_typ in
    let ty2 = sc2.sa_typ + sc1.sa_aut.num_states in
    let ty3 = sc3.sa_typ + sc1.sa_aut.num_states + sc2.sa_aut.num_states in
    scheme_update false sc1 sc2;
    scheme_update false sc1 sc3;
    let w1 = new_state sc1.sa_aut in
    Hashtbl.add sc1.sa_aut.data w1 (true, AHSet.empty, ALMap.empty);
    let w2 = new_state sc1.sa_aut in
    Hashtbl.add sc1.sa_aut.data w2 (false, AHSet.empty, ALMap.empty);
    sc1.sa_flow <- (w2, w1) :: sc1.sa_flow;
    let w3 = new_state sc1.sa_aut in
    Hashtbl.add sc1.sa_aut.data w3
      (false, AHSet.singleton (HIdent builtin_int_id), ALMap.empty);
    sc1.sa_typ <- w1;
    biunify sc1 ty1 w3;
    biunify sc1 ty2 w2;
    biunify sc1 ty3 w2;
    sc1, T.IfZero (nt1, nt2, nt3)
  | S.Tuple l ->
    let l = List.map (cook_term env) l in
    let sc, qs = scheme_join_many (List.map fst l) in
    let w = new_state sc.sa_aut in
    let arity = List.length l in
    let arrows = from_bindings (List.mapi (fun i q ->
        LTuple (arity, i), (ISet.singleton q)) qs) in
    Hashtbl.add sc.sa_aut.data w (true, AHSet.singleton (HTuple arity), arrows);
    sc.sa_typ <- w;
    sc, (T.Tuple (List.map snd l))
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
    List.iter2 (fun (place, (sc, _)) ety ->
        let q, eaut = to_aut false ety in
        let esc = {
          sa_aut = eaut ;
          sa_typ = q ;
          sa_hypotheses = Atom.Map.empty ;
          sa_flow = [] ;
        } in
        let ety = q + sc.sa_aut.num_states in
        scheme_update false sc esc;
        biunify sc sc.sa_typ ety
    ) args cargs;
    let sc, _ = scheme_join_many (List.map (fun (_, (sc, _)) -> sc) args) in
    (* TODO: if effect, add to list *)
    let nt =
      if is_effect then
        let (_, nt, _) = Atom.Map.find tname env.effect_defs in nt
      else
        T.Tident tname
    in
    let q, raut = to_aut true nt in
    let rsc = {
      sa_aut = raut ;
      sa_typ = q ;
      sa_hypotheses = Atom.Map.empty ;
      sa_flow = [] ;
    } in
    let rty = q + sc.sa_aut.num_states in
    scheme_update false sc rsc;
    sc.sa_typ <- rty;
    sc, T.Constructor ((catom, ctag, is_effect), List.map (fun (_, (_, t)) -> t) args)
  | S.Match (t, l) ->
    (*
    let sc, nt = cook_term env t in
    let rty = T.Tvar (TV.create ()) in
    let nl = List.map (fun (p, t1) ->
      let np, dv = cook_pattern_or_effect env sc.typ rty p in
      let nenv = Smap.fold (fun x (a, t) env -> add_bound x a env) dv env in
      let sc1, nt1 = cook_term nenv t1 in
      check_unify t1.S.place env sc1.typ rty;
      let nh = Smap.fold (fun _ (a, t) h ->
          try
            let ty, place = Atom.Map.find a h in
            check_unify place env ty t;
            Atom.Map.remove a h
          with Not_found -> h
      ) dv sc1.hypotheses in
      let nsc = {
        hypotheses = nh ;
        typ = rty ;
      } in
      (nsc, (np, nt1))
    ) l in
    let nsc = {
      hypotheses = List.fold_left (fun h (sc, _) -> unify_hyp env h sc.hypotheses) sc.hypotheses nl ;
      typ = rty ;
    } in
    nsc, T.Match (nt, List.map snd nl) *) assert false

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
    let sc, t = cook_term env t in
    let nenv, nx = add_gen x sc env in
    (nenv, nx, sc, t)
  | S.Recursive, { S.value = S.Lam (y, t) ; _ } ->
    let sc, nx, ny, nt =
      let nenv, nx = add x env in
      let nenv, ny = add y nenv in
      let sc, nt = cook_term nenv t in
      let w = new_state sc.sa_aut in
      let nxt =
        try
          let ty, _ = Atom.Map.find ny sc.sa_hypotheses in
          sc.sa_hypotheses <- Atom.Map.remove ny sc.sa_hypotheses;
          from_bindings [LArrowsrc, ISet.singleton ty ;
                         LArrowdst, ISet.singleton sc.sa_typ]
        with Not_found ->
          from_bindings [LArrowdst, ISet.singleton sc.sa_typ]
      in
      Hashtbl.add sc.sa_aut.data w (true, AHSet.singleton HArrow, nxt);
      sc.sa_typ <- w;
      (try
         let ty, place = Atom.Map.find nx sc.sa_hypotheses in
         biunify sc sc.sa_typ ty;
         sc.sa_hypotheses <- Atom.Map.remove nx sc.sa_hypotheses
       with Not_found -> ());
      sc, nx, ny, nt
    in
    let nenv, nx2 = add_gen x sc env in
    (nenv, nx2, sc, T.Lam (T.Self nx, ny, nt))
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

(*
let print_schema ff { vars ; typ } =
  let fv = Ty.fvars typ in
  Ty.print (TV.get_print_names fv vars) 0 ff typ
*)

let rec cook_program env = function
  | { S.value = S.DTerm t ; _ } :: p ->
    let a = Atom.fresh "_" in
    let sc, nt = cook_term env t in
    assert (Atom.Map.is_empty sc.sa_hypotheses);
    (* unify_row row T.Rempty; (* TODO allow io *) *)
    T.Let (a, nt, cook_program env p)
  | { S.value = S.DLet (recursive, x, t) ; _ } :: p ->
    let env, nx, sc, nt = cook_let env recursive x t in
    (* unify_row row T.Rempty; (* TODO allow io *) *)
    assert (Atom.Map.is_empty sc.sa_hypotheses);
    Format.eprintf "val %s : @[<hv>%a@]@." x print_scheme (of_scheme_aut sc);
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
