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

[@@deriving show { with_path = false }]

module rec TyE : sig
  type ep = TyESet.t * bool
  type t = {
    id : int ;
    polarity : bool ;
    mutable flows : ep Atom.Map.t * ep ;
  }
  val compare : t -> t -> int
  val create : bool -> t
  val create_flow_pair : unit -> t * t
  val common_domain : t -> t -> unit
  val extend : Atom.atom -> t -> unit
  val add_flow_edge : Atom.atom option -> t -> t -> unit
  val merge : bool -> t -> t -> t
end = struct
  type ep = TyESet.t * bool
  type t = {
    id : int ;
    polarity : bool ;
    mutable flows : ep Atom.Map.t * ep ;
  }
  let compare t1 t2 = compare t1.id t2.id
  let r = ref 0
  let create polarity =
    let z = !r in
    r := z + 1;
    { id = z ; polarity = polarity ; flows = (Atom.Map.empty, (TyESet.empty, false)) }
  let access t =
    let seen = ref TyESet.empty in
    let to_see = ref (TyESet.singleton t) in
    while not (TyESet.is_empty !to_see) do
      let t = TyESet.choose !to_see in
      to_see := TyESet.remove t !to_see;
      seen := TyESet.add t !seen;
      let ts = fst (snd t.flows) in
      let ts = TyESet.diff ts !seen in
      to_see := TyESet.union ts !to_see
    done;
    !seen
  let extend_one name t =
    if Atom.Map.mem name (fst t.flows) then ()
    else
      t.flows <- (Atom.Map.add name (snd t.flows) (fst t.flows), snd t.flows)
  let extend name t =
    if Atom.Map.mem name (fst t.flows) then ()
    else
      TyESet.iter (extend_one name) (access t)
  let common_domain t1 t2 =
    let d1 = Atom.Map.domain (fst t1.flows) in
    let d2 = Atom.Map.domain (fst t2.flows) in
    Atom.Set.iter (fun name -> extend name t1) (Atom.Set.diff d2 d1);
    Atom.Set.iter (fun name -> extend name t2) (Atom.Set.diff d1 d2)
  let add_flow_edge name t1 t2 =
    match name with
    | Some name ->
      extend name t1; extend name t2;
      common_domain t1 t2;
      let qs1, b1 = Atom.Map.find name (fst t1.flows) in
      let qs2, b2 = Atom.Map.find name (fst t2.flows) in
      t1.flows <- (Atom.Map.add name (TyESet.add t2 qs1, b1) (fst t1.flows),
                   snd t1.flows);
      t2.flows <- (Atom.Map.add name (TyESet.add t1 qs2, b2) (fst t2.flows),
                   snd t2.flows)
    | None ->
      common_domain t1 t2;
      let (m1, (qs1, b1)) = t1.flows in
      let (m2, (qs2, b2)) = t2.flows in
      t1.flows <- (m1, (TyESet.add t2 qs1, b1));
      t2.flows <- (m2, (TyESet.add t1 qs2, b2))
  let create_flow_pair () =
    let qp = create true in
    let qm = create false in
    qp.flows <- (Atom.Map.empty, (TyESet.singleton qm, false));
    qm.flows <- (Atom.Map.empty, (TyESet.singleton qp, false));
    (qp, qm)
  let merge pol t1 t2 =
    let q = create pol in
    if pol then begin
      assert (snd (snd t1.flows) = false);
      assert (snd (snd t2.flows) = false)
    end;
    common_domain t1 t2;
    let m = Atom.Map.merge (fun _ u1 u2 ->
        match u1, u2 with
        | None, None -> None
        | None, Some u | Some u, None -> Some u
        | Some (qs1, b1), Some (qs2, b2) ->
          Some (TyESet.union qs1 qs2, b1 || b2)
      ) (fst t1.flows) (fst t2.flows)
    in
    let b = snd (snd t1.flows) || snd (snd t2.flows) in
    q.flows <- (m, (TyESet.empty, b));
    Atom.Map.iter (fun name (qs, _) ->
      TyESet.iter (add_flow_edge (Some name) q) qs;
    ) m;
    TyESet.iter (add_flow_edge None q) (fst (snd t1.flows));
    TyESet.iter (add_flow_edge None q) (fst (snd t2.flows));
    q
end

and TyESet : Set.S with type elt = TyE.t = Set.Make(TyE)

module rec TyC : sig
  type t =
    | Tident of arg list * tname
    | Tarrow of TySSet.t * TyE.t * TySSet.t
    | Tproduct of TySSet.t list
  and arg =
    | AType of TySSet.t variance
    | AEff of TyE.t variance
  and 'a variance =
    | VNone
    | VPos of 'a
    | VNeg of 'a
    | VPosNeg of 'a * 'a
end = struct
  type t =
    | Tident of arg list * tname
    | Tarrow of TySSet.t * TyE.t * TySSet.t
    | Tproduct of TySSet.t list
  and arg =
    | AType of TySSet.t variance
    | AEff of TyE.t variance
  and 'a variance =
    | VNone
    | VPos of 'a
    | VNeg of 'a
    | VPosNeg of 'a * 'a
end

and TyCSet : sig
  type t = TyC.t list
  val merge : bool -> t -> t -> t
  val map : (bool -> TyC.t -> TyC.t) -> bool -> t -> t
  val iter : (bool -> TyC.t -> unit) -> bool -> t -> unit
  val map_flatten : (bool -> TyC.t -> t) -> bool -> t -> t
  val singleton : bool -> TyC.t -> t
  val need_resolve : bool -> bool -> t -> t -> bool
end = struct
  type t = TyC.t list
  let merge_variance pol merge v1 v2 =
    let open TyC in
    match v1, v2 with
    | VNone, v | v, VNone -> v
    | VPos qs1, VPos qs2 -> VPos (merge pol qs1 qs2)
    | VNeg qs1, VNeg qs2 -> VNeg (merge (not pol) qs1 qs2)
    | VPos qps1, VPosNeg (qps2, qns2) | VPosNeg (qps2, qns2), VPos qps1 ->
      VPosNeg (merge pol qps1 qps2, qns2)
    | VNeg qns1, VPosNeg (qps2, qns2) | VPosNeg (qps2, qns2), VNeg qns1 ->
      VPosNeg (qps2, merge (not pol) qns1 qns2)
    | VPosNeg (qps1, qns1), VPosNeg (qps2, qns2) ->
      VPosNeg (merge pol qps1 qps2, merge (not pol) qns1 qns2)
    | VPos qps, VNeg qns | VNeg qns, VPos qps -> VPosNeg (qps, qns)
  let merge_arg pol a1 a2 =
    let open TyC in
    match a1, a2 with
    | AType v1, AType v2 ->
      AType (merge_variance pol (fun _ -> TySSet.union) v1 v2)
    | AEff v1, AEff v2 ->
      AEff (merge_variance pol TyE.merge v1 v2)
    | _ -> assert false
  let rec add pol x l =
    let open TyC in
    match x, l with
    | _, [] -> [x]
    | Tident (vs1, n1), Tident (vs2, n2) :: l1 when Atom.equal n1 n2 ->
      assert (List.length vs1 = List.length vs2);
      Tident (List.map2 (merge_arg pol) vs1 vs2, n1) :: l1
    | Tarrow (qsa1, qsb1, qsc1), Tarrow (qsa2, qsb2, qsc2) :: l1 ->
      Tarrow (TySSet.union qsa1 qsa2, TyE.merge pol qsb1 qsb2,
              TySSet.union qsc1 qsc2) :: l1
    | Tproduct qsl1, Tproduct qsl2 :: l1 when List.length qsl1 = List.length qsl2 ->
      Tproduct (List.map2 TySSet.union qsl1 qsl2) :: l1
    | x, y :: l -> y :: add pol x l
  let rec merge polarity l1 l2 =
    match l1 with
    | [] -> l2
    | t :: l1 -> merge polarity l1 (add polarity t l2)
  let rec iter f pol l =
    match l with
    | [] -> ()
    | t :: l -> f pol t; iter f pol l
  let rec map f pol l =
    match l with
    | [] -> []
    | t :: l -> add pol (f pol t) (map f pol l)
  let rec map_flatten f pol l =
    match l with
    | [] -> []
    | t :: l -> merge pol (f pol t) (map_flatten f pol l)
  let singleton _ t = [t]
  let need_resolve _ _ l1 l2 =
    let open TyC in
    match l1, l2 with
    | [], _ | _, [] -> false
    | [Tident (_, n1)], [Tident (_, n2)] when Atom.equal n1 n2 -> false
    | _ -> true
end

and TyS : sig
  type t = {
    id : int ;
    polarity : bool ;
    mutable constructors : TyCSet.t ;
    mutable flow : TySSet.t ;
  }
  val compare : t -> t -> int
  val create : bool -> t
  val create_flow_pair : unit -> t * t
  val add_flow_edge : t -> t -> unit
end = struct
  type t = {
    id : int ;
    polarity : bool ;
    mutable constructors : TyCSet.t ;
    mutable flow : TySSet.t ;
  }
  let compare x1 x2 = compare x1.id x2.id
  let r = ref 0
  let create b =
    let t = !r in
    incr r;
    { id = t ; polarity = b ; constructors = [] ; flow = TySSet.empty }
  let create_flow_pair () =
    let q1 = create true in
    let q2 = create false in
    q1.flow <- TySSet.singleton q2;
    q2.flow <- TySSet.singleton q1;
    (q1, q2)
  let add_flow_edge q1 q2 =
    q1.flow <- TySSet.add q2 q1.flow;
    q2.flow <- TySSet.add q1 q2.flow
end

and TySSet : Set.S with type elt = TyS.t = Set.Make(TyS)

module TySMap = Map.Make(TyS)
module TySPSet = Set.Make(struct
    type t = TyS.t * TyS.t
    let compare (x1, y1) (x2, y2) =
      let c = TyS.compare x1 x2 in
      if c = 0 then TyS.compare y1 y2 else c
end)

let arrow_option polarity q1 eff q2 =
  let w = TyS.create polarity in
  let qs1 =
    match q1 with
    | None -> TySSet.empty
    | Some q1 -> TySSet.singleton q1
  in
  let qs2 = TySSet.singleton q2 in
  w.TyS.constructors <- TyCSet.singleton polarity (TyC.Tarrow(qs1, eff, qs2));
  w

let arrow polarity q1 eff q2 = arrow_option polarity (Some q1) eff q2

let product polarity l =
  let w = TyS.create polarity in
  let qsl = List.map TySSet.singleton l in
  w.TyS.constructors <- TyCSet.singleton polarity (TyC.Tproduct qsl);
  w

let ident polarity n vs =
  let w = TyS.create polarity in
  w.TyS.constructors <- TyCSet.singleton polarity (TyC.Tident (vs, n));
  w

let var_succ = function
  | TyC.VNone -> TySSet.empty
  | TyC.VPos qs | TyC.VNeg qs -> qs
  | TyC.VPosNeg (qps, qns) -> TySSet.union qps qns

let arg_succ = function
  | TyC.AEff _ -> TySSet.empty
  | TyC.AType v -> var_succ v

let tyc_succ = function
  | TyC.Tident (vs, _) ->
    List.fold_left TySSet.union TySSet.empty (List.map arg_succ vs)
  | TyC.Tarrow (q1, _, q2) -> TySSet.union q1 q2
  | TyC.Tproduct l -> List.fold_left TySSet.union TySSet.empty l

let tys_succ q =
  List.fold_left (fun qs t -> TySSet.union qs (tyc_succ t))
    TySSet.empty q.TyS.constructors

let decompose_flow elms =
  let fl = TySSet.fold
      (fun q m -> TySMap.add q (TySSet.inter q.TyS.flow elms) m)
      elms TySMap.empty in
  let result = ref [] in
  let rec loop fl =
    let best = ref (TySSet.empty, TySSet.empty) in
    let best_v = ref 0 in
    TySMap.iter (fun _ qs1 ->
      match TySSet.elements qs1 with
      | [] -> ()
      | q2 :: qs ->
        let qs2 = List.fold_left
            (fun qs2 q2 -> TySSet.inter qs2 (TySMap.find q2 fl))
            (TySMap.find q2 fl) qs
        in
        let v = (TySSet.cardinal qs1) * (TySSet.cardinal qs2) in
        if v > !best_v then begin
          best_v := v;
          best := (qs1, qs2)
        end
    ) fl;
    if !best_v > 0 then begin
      let qs1, qs2 = !best in
      result := (qs1, qs2) :: !result;
      let fl = TySMap.mapi (fun q qs ->
        if TySSet.mem q qs1 then
          TySSet.diff qs qs2
        else if TySSet.mem q qs2 then
          TySSet.diff qs qs1
        else
          qs
      ) fl in
      let fl = TySMap.filter (fun _ qs -> not (TySSet.is_empty qs)) fl in
      loop fl
    end
  in
  loop fl;
  !result

module TyEMap = Map.Make(TyE)

let decompose_flow_e name elms =
  let get_flow q =
    match name with
    | None -> fst (snd q.TyE.flows)
    | Some name -> fst (try Atom.Map.find name (fst q.TyE.flows) with Not_found -> snd q.TyE.flows)
  in
  let fl = TyESet.fold
      (fun q m -> TyEMap.add q (TyESet.inter (get_flow q) elms) m)
      elms TyEMap.empty in
  let result = ref [] in
  let rec loop fl =
    let best = ref (TyESet.empty, TyESet.empty) in
    let best_v = ref 0 in
    TyEMap.iter (fun _ qs1 ->
      match TyESet.elements qs1 with
      | [] -> ()
      | q2 :: qs ->
        let qs2 = List.fold_left
            (fun qs2 q2 -> TyESet.inter qs2 (TyEMap.find q2 fl))
            (TyEMap.find q2 fl) qs
        in
        let v = (TyESet.cardinal qs1) * (TyESet.cardinal qs2) in
        if v > !best_v then begin
          best_v := v;
          best := (qs1, qs2)
        end
    ) fl;
    if !best_v > 0 then begin
      let qs1, qs2 = !best in
      result := (qs1, qs2) :: !result;
      let fl = TyEMap.mapi (fun q qs ->
        if TyESet.mem q qs1 then
          TyESet.diff qs qs2
        else if TyESet.mem q qs2 then
          TyESet.diff qs qs1
        else
          qs
      ) fl in
      let fl = TyEMap.filter (fun _ qs -> not (TyESet.is_empty qs)) fl in
      loop fl
    end
  in
  loop fl;
  !result

module SSet = Set.Make(String)

let pfprintf (level : int) lprotect rprotect ff fmt =
  if level >= lprotect then Format.fprintf ff "(";
  Format.kfprintf (fun ff -> if level >= rprotect then Format.fprintf ff ")")
    ff fmt

let rec print_tyc st level pol ff t =
  match t with
  | TyC.Tident ([], n) ->
    Format.fprintf ff "%s" (Atom.hint n)
  | TyC.Tident (vs, n) ->
    Format.fprintf ff "%t %s" (fun ff ->
        List.iteri (fun i va ->
            if i > 0 then Format.fprintf ff ", ";
            print_arg st 10 pol ff va) vs
    ) (Atom.hint n)
  | TyC.Tarrow (qs1, eff, qs2) ->
    pfprintf level 3 3 ff "%a -[@[<hv>%a@]]->@ @[<hv>%a@]"
      (print_tyss st 3 (not pol)) qs1
      (print_eff st 0 pol) eff
      (print_tyss st 2 pol) qs2
  | TyC.Tproduct l ->
    pfprintf level 4 4 ff "%t" (fun ff ->
      List.iteri (fun i qs ->
        if i > 0 then Format.fprintf ff " *@ ";
        Format.fprintf ff "%a" (print_tyss st 4 pol) qs
      ) l
    )

and print_var_t st _ pol ff va =
  match va with
  | TyC.VNone -> Format.fprintf ff "_"
  | TyC.VPos qs -> Format.fprintf ff "+%a" (print_tyss st 10 pol) qs
  | TyC.VNeg qs -> Format.fprintf ff "-%a" (print_tyss st 10 (not pol)) qs
  | TyC.VPosNeg (qsp, qsn) ->
    Format.fprintf ff "[+%a -%a]"
      (print_tyss st 10 pol) qsp (print_tyss st 10 (not pol)) qsn

and print_var_e st _ pol ff va =
  match va with
  | TyC.VNone -> Format.fprintf ff "_"
  | TyC.VPos qs -> Format.fprintf ff "+[%a]" (print_eff st 10 pol) qs
  | TyC.VNeg qs -> Format.fprintf ff "-[%a]" (print_eff st 10 (not pol)) qs
  | TyC.VPosNeg (qsp, qsn) ->
    Format.fprintf ff "[+[%a] -[%a]]"
      (print_eff st 10 pol) qsp (print_eff st 10 (not pol)) qsn

and print_arg st level pol ff = function
  | TyC.AType va -> print_var_t st level pol ff va
  | TyC.AEff va -> print_var_e st level pol ff va

and print_eff st _ pol ff t =
  let eff, def = t.TyE.flows in
  let _, _, _, (enamee, _) = st in
  let get name = try Atom.Map.find name eff with Not_found -> def in
  let l = List.map (fun (name, _) -> (Some name, get name))
      (Atom.Map.bindings enamee) @ [(None, def)] in
  let printed = ref false in
  List.iter (fun (name, d) ->
      printed := print_ep st 6 pol name ff d !printed
    ) l

and print_ep st _ pol name ff (es, b) needs_sep =
  let _, _, _, (enamee, enamed) = st in
  let mp = match name with None -> enamed | Some name -> Atom.Map.find name enamee in
  let get t = try TyEMap.find t mp with Not_found -> SSet.empty in
  let fv = List.fold_left SSet.union SSet.empty
      (List.map get (TyESet.elements es)) in
  if SSet.is_empty fv && pol && not b then
    false
  else if SSet.is_empty fv && (pol || not b) then begin
    match name with
    | None -> false
    | Some name ->
      if needs_sep then Format.fprintf ff " | ";
      Format.fprintf ff "%s" (Atom.hint name);
      true
  end else begin
    if needs_sep then Format.fprintf ff " | ";
    (match name with
     | None -> ()
     | Some name -> Format.fprintf ff "%s : " (Atom.hint name));
    let sep = ref false in
    if b && not pol then (Format.fprintf ff "no"; sep := true);
    SSet.iter (fun x ->
        if !sep then Format.fprintf ff " ";
        Format.fprintf ff "%s" x;
        sep := true
      ) fv;
  true
  end

and print_tyss st level pol ff qs =
  let l = TySSet.elements qs in
  match l with
  | [] -> if pol then Format.fprintf ff "Bot" else Format.fprintf ff "Top"
  | [q] -> print_tys st level ff q
  | _ ->
    let lv, op = if pol then 5, "|" else 7, "&" in
    pfprintf level lv lv ff "%t" (fun ff ->
      List.iteri (fun i q ->
        if i > 0 then Format.fprintf ff " %s@ " op;
        Format.fprintf ff "%a" (print_tys st (lv + 1)) q
      ) l)

and print_tys st level ff q =
  let (flow_vars, rec_vars, rec_seen, _) = st in
  if TySSet.mem q !rec_seen then
    Format.fprintf ff "%s" (TySMap.find q rec_vars)
  else
    let l1 = List.map (fun t lv -> print_tyc st lv q.TyS.polarity ff t)
        q.TyS.constructors in
    let l2 = List.map (fun name _ -> Format.fprintf ff "%s" name)
        (try TySMap.find q flow_vars with Not_found -> []) in
    let lev, op = if q.TyS.polarity then 5, "|" else 7, "&" in
    let finish lv =
      match l1 @ l2 with
      | [] -> Format.fprintf ff (if q.TyS.polarity then "Bot" else "Top")
      | [f] -> f lv
      | l ->
        if lv >= lev then Format.fprintf ff "(";
        List.iteri (fun i f ->
            if i > 0 then Format.fprintf ff " %s@ " op;
            f (lev + 1)
        ) l;
        if lv >= lev then Format.fprintf ff ")"
    in
    if TySMap.mem q rec_vars then begin
      if level >= 1 then Format.fprintf ff "(";
      rec_seen := TySSet.add q !rec_seen;
      finish 1;
      Format.fprintf ff " as %s" (TySMap.find q rec_vars);
      if level >= 1 then Format.fprintf ff ")"
    end else finish level

let make_print_state flow_vars rec_vars fveff =
  (flow_vars, rec_vars, ref TySSet.empty, fveff)

let get_print_name i =
  let s = String.make 1 (char_of_int ((i mod 15) + 97)) in
  let s = if i > 26 then s ^ string_of_int (i / 15) else s in
  "'" ^ s

let get_eff_print_name i =
  let s = String.make 1 (char_of_int ((i mod 11) + 112)) in
  let s = if i > 26 then s ^ string_of_int (i / 11) else s in
  "!" ^ s

let var_add r = function
  | TyC.VNone -> r
  | TyC.VPos e | TyC.VNeg e -> TyESet.add e r
  | TyC.VPosNeg (e1, e2) -> TyESet.add e1 (TyESet.add e2 r)

let arg_add r = function
  | TyC.AEff v -> var_add r v
  | TyC.AType _ -> r

let tye_acc qs =
  let r = ref TyESet.empty in
  TySSet.iter (fun q ->
    TyCSet.iter (fun _ c ->
      match c with
      | TyC.Tarrow (_, e, _) -> r := TyESet.add e !r
      | TyC.Tident (l, _) ->
        r := List.fold_left arg_add !r l
      | _ -> ()
    ) q.TyS.polarity q.TyS.constructors
  ) qs;
  !r

let enames_acc es =
  TyESet.fold (fun e s -> Atom.Set.union s (Atom.Map.domain (fst e.TyE.flows)))
    es Atom.Set.empty

let prepare_printing l le =
  let needs_rec = ref TySSet.empty in
  let explored = ref TySSet.empty in
  let rec loop seen q =
    if TySSet.mem q seen then
      needs_rec := TySSet.add q !needs_rec
    else if TySSet.mem q !explored then
      ()
    else begin
      explored := TySSet.add q !explored;
      let nseen = TySSet.add q seen in
      TySSet.iter (loop nseen) (tys_succ q)
    end
  in
  List.iter (loop TySSet.empty) l;
  let eff = List.fold_left (fun es e -> TyESet.add e es) (tye_acc !explored) le in
  let en = enames_acc eff in
  let ec = ref 0 in
  let do_eff name =
    let fvs = decompose_flow_e name eff in
    let fv = ref TyEMap.empty in
    List.iter (fun (qs1, qs2) ->
      let name = get_eff_print_name !ec in
      incr ec;
      TyESet.iter (fun q ->
        fv := TyEMap.add q (SSet.add name
                            (try TyEMap.find q !fv with Not_found -> SSet.empty)) !fv
      ) (TyESet.union qs1 qs2)
    ) fvs;
    !fv
  in
  let fveff = ref Atom.Map.empty in
  Atom.Set.iter (fun name -> fveff := Atom.Map.add name (do_eff (Some name)) !fveff) en;
  let fveff = (!fveff, do_eff None) in
  let fvs = decompose_flow !explored in
  let fv = ref TySMap.empty in
  List.iteri (fun i (qs1, qs2) ->
      let name = get_print_name i in
      TySSet.iter (fun q ->
          fv := TySMap.add q (name ::
                              try TySMap.find q !fv with Not_found -> []) !fv
      ) (TySSet.union qs1 qs2)
    ) fvs;
  let n = List.length fvs in
  let recv = ref TySMap.empty in
  List.iteri (fun i q ->
      recv := TySMap.add q (get_print_name (i + n)) !recv
  ) (TySSet.elements !needs_rec);
  make_print_state !fv !recv fveff

let accessible l =
  let explored = ref TySSet.empty in
  let rec loop q =
    if not (TySSet.mem q !explored) then begin
      explored := TySSet.add q !explored;
      TySSet.iter loop (tys_succ q)
    end
  in
  List.iter loop l;
  !explored

let prepare_copy l le =
  let acc = accessible l in
  let eacc = List.fold_left (fun es e -> TyESet.add e es) (tye_acc acc) le in
  let em = TyESet.fold (fun q m -> TyEMap.add q (TyE.create q.TyE.polarity) m)
      eacc TyEMap.empty in
  let m = TySSet.fold (fun q m -> TySMap.add q (TyS.create q.TyS.polarity) m)
      acc TySMap.empty in
  let tyss_copy = TySSet.map (fun q2 -> TySMap.find q2 m) in
  let effs_copy = TyESet.map (fun e -> TyEMap.find e em) in
  let em_copy (s, b) = (effs_copy (TyESet.inter s eacc), b) in
  let fl_copy (eff, def) = (Atom.Map.map em_copy eff, em_copy def) in
  TyEMap.iter (fun e ne ->
      ne.TyE.flows <- fl_copy e.TyE.flows) em;
  let eff_copy eff = TyEMap.find eff em in
  let var_copy cp = function
    | TyC.VNone -> TyC.VNone
    | TyC.VPos qs -> TyC.VPos (cp qs)
    | TyC.VNeg qs -> TyC.VNeg (cp qs)
    | TyC.VPosNeg (qps, qns) -> TyC.VPosNeg (cp qps, cp qns)
  in
  let arg_copy = function
    | TyC.AType v -> TyC.AType (var_copy tyss_copy v)
    | TyC.AEff v -> TyC.AEff (var_copy eff_copy v)
  in
  let tyc_copy = function
    | TyC.Tident (vs, n) -> TyC.Tident (List.map arg_copy vs, n)
    | TyC.Tarrow (qs1, eff, qs2) ->
      TyC.Tarrow (tyss_copy qs1, eff_copy eff, tyss_copy qs2)
    | TyC.Tproduct l -> TyC.Tproduct (List.map tyss_copy l)
  in
  TySMap.iter (fun q nq ->
      nq.TyS.flow <- tyss_copy (TySSet.inter q.TyS.flow acc);
      nq.TyS.constructors <- List.map tyc_copy q.TyS.constructors
  ) m;
  (m, em)

let copy st q =
  TySMap.find q (fst st)

let tyss_copy st = TySSet.map (copy st)

let eff_copy st e = TyEMap.find e (snd st)

let copy_one q =
  copy (prepare_copy [q] []) q
