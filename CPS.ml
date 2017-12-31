(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

let lambda_let (lam : T.block) (body : T.value -> T.term) : T.term =
  let f = Atom.fresh "cps_lambda_let" in
  T.LetBlo (f, lam, body (T.vvar f))

let continuation_to_fct (t : T.value) (body : T.value -> T.term) : T.term =
  let k = Atom.fresh "cps_cont" in
  let cnt = Atom.fresh "cps_cnt" in
  lambda_let (T.Lam (T.NoSelf, [k; cnt], T.TailCall (t, [T.vvar k]))) body

let fct_to_continuation (t : T.value) (body : T.value -> T.term) : T.term =
  let cont_arg = Atom.fresh "cps_cont_arg" in
  let ex_arg = Atom.fresh "cps_ex_arg" in
  lambda_let (T.Lam (T.NoSelf, [cont_arg],
    lambda_let (T.Lam (T.NoSelf, [ex_arg], T.Exit)) (fun ex ->
      T.ContCall (t, ex, [T.vvar cont_arg])))) body

let rec cps (t : S.term) (k : T.value) : T.term =
  match t with
  | S.Var v -> T.TailCall (k, [T.vvar v])
  | S.Lam (self, var, body) ->
    let cont = Atom.fresh "cps_cont" in
    let args, body1 = cps_lam body [var] in
    lambda_let (T.Lam (self, List.rev (cont :: args), cps body1 (T.vvar cont)))
      (fun f -> T.TailCall (k, [f]))
  | S.App (t1, t2) ->
    cps_app t k []
  | S.Lit n -> T.TailCall (k, [T.VLit n])
  | S.BinOp (t1, op, t2) ->
    let bl = Atom.fresh "cps_bl" in
    let br = Atom.fresh "cps_br" in
    let w =
      lambda_let (T.Lam (T.NoSelf, [br],
                         T.TailCall (k, [T.VBinOp (T.vvar bl, op, T.vvar br)])))
        (cps t2) in
    lambda_let (T.Lam (T.NoSelf, [bl], w)) (cps t1)
  | S.Print t ->
    let pr = Atom.fresh "cps_pr" in
    lambda_let (T.Lam (T.NoSelf, [pr],
                       T.Print (T.vvar pr, T.TailCall (k, [T.vvar pr]))))
      (cps t)
  | S.CallCc t ->
    let f = Atom.fresh "cps_callcc" in
    lambda_let (T.Lam (T.NoSelf, [f],
      continuation_to_fct k (fun kf ->
        T.ContCall (T.vvar f, k, [kf]))
    )) (cps t)
  | S.Let (x, t1, t2) ->
    lambda_let (T.Lam (T.NoSelf, [x], cps t2 k)) (cps t1)
  | S.IfZero (t1, t2, t3) ->
    let cond = Atom.fresh "cps_if" in
    lambda_let (T.Lam (T.NoSelf, [cond],
                       T.IfZero (T.vvar cond, cps t2 k, cps t3 k))) (cps t1)
  | S.Match (t, pl) ->
    let match_var = Atom.fresh "cps_match_var" in
    lambda_let (T.Lam (T.NoSelf, [match_var],
      lambda_let (T.Lam (T.NoSelf, [], T.Exit)) (fun handle ->
        cps_match [T.vvar match_var]
          (List.map (fun (p, t) -> [p], cps t k) pl) handle)
    )) (cps t)
  | S.Tuple l ->
    let vars = List.map (fun _ -> Atom.fresh "cps_tuple_var") l in
    let tpl = Atom.fresh "cps_tuple" in
    List.fold_left2 (fun k t name ->
      lambda_let (T.Lam (T.NoSelf, [name], k)) (cps t)
      ) (T.LetBlo (tpl, T.Tuple (T.vvars vars),
                   T.TailCall (k, [T.vvar tpl]))) l vars
  | S.Constructor ((_, tag), l) ->
    let vars = List.map (fun _ -> Atom.fresh "cps_constructor_var") l in
    let ctr = Atom.fresh "cps_constructor" in
    List.fold_left2 (fun k t name ->
      lambda_let (T.Lam (T.NoSelf, [name], k)) (cps t)
      ) (T.LetBlo (ctr, T.Constructor (tag, T.vvars vars),
                   T.TailCall (k, [T.vvar ctr]))) l vars


and cps_app (t : S.term) (k : T.value) (args : T.value list) : T.term =
  match t with
  | S.App (t1, t2) ->
    let appr = Atom.fresh "cps_appr" in
    lambda_let (T.Lam (T.NoSelf, [appr],
      cps_app t1 k (T.vvar appr :: args)
                      )) (cps t2)
  | _ ->
    let appl = Atom.fresh "cps_appl" in
    lambda_let (T.Lam (T.NoSelf, [appl],
      T.ContCall (T.vvar appl, k, args))) (cps t)

and cps_lam (t : S.term) (args : T.variable list) : T.variable list * S.term =
  match t with
  | S.Lam (T.NoSelf, var, body) ->
    cps_lam body (var :: args)
  | _ -> (args, t)

and split_matching matching =
  let rec aux first rest =
    match rest with
    | ((p :: _, _) as x) :: r ->
      (match first, p with
       | S.PTuple _, S.PTuple _
       | S.PConstructor _, S.PConstructor _
       | S.PVar _, S.PVar _ ->
         let l1, l2 = aux first r in
         x :: l1, l2
       | _ -> [], rest)
    | _ -> [], rest
  in
  match matching with
  | (first :: _, _) :: _ -> aux first matching
  | _ -> [], matching

and flatten_tuples matching =
  List.map (fun z -> match z with
      | S.PTuple l1 :: l2, t -> l1 @ l2, t
      | _ -> assert false) matching

and remove_top_vars matching v =
  List.map (fun z -> match z with
      | S.PVar v1 :: l, t -> l, T.LetVal (v1, v, t)
      | _ -> assert false
    ) matching

and remove_constructors matching =
  let tbl = Hashtbl.create 17 in
  List.iter (fun z -> match z with
      | S.PConstructor ((_, tag), l1) :: l2, t ->
        let vars, patterns =
          try Hashtbl.find tbl tag
          with Not_found ->
            List.map (fun _ -> Atom.fresh "match_destruct_var") l1, []
        in
        Hashtbl.replace tbl tag (vars, (l1 @ l2, t) :: patterns)
      | _ -> assert false
    ) matching;
  Hashtbl.fold (fun tag d l -> (tag, d) :: l) tbl []

and cps_match
    (match_terms : T.value list)
    (matching : (S.pattern list * T.term) list)
    (handle : T.value) : T.term =
  match matching with
  | [] -> T.TailCall (handle, [])
  | (pl1, t) :: l ->
    match pl1 with
    | [] -> t
    | S.POr (p1, p2) :: pl ->
      (* FIXME: fix exponential blowup *)
      cps_match match_terms ((p1 :: pl, t) :: (p2 :: pl, t) :: l) handle
    | S.PTuple pl :: _ ->
      let tuples, rest = split_matching matching in
      let tvars = List.map (fun _ -> Atom.fresh "match_tuple_var") pl in
      lambda_let (T.Lam (T.NoSelf, [], cps_match match_terms rest handle))
        (fun handle2 ->
           T.DestructTuple (List.hd match_terms, tvars,
             cps_match (T.vvars tvars @ List.tl match_terms)
               (flatten_tuples tuples) handle2
           )
        )
    | S.PVar _ :: _ ->
      let vars, rest = split_matching matching in
      lambda_let (T.Lam (T.NoSelf, [], cps_match match_terms rest handle))
        (fun handle2 ->
           cps_match (List.tl match_terms)
             (remove_top_vars vars (List.hd match_terms)) handle2
        )
    | S.PConstructor _ :: _ ->
      let constructors, rest = split_matching matching in
      let cl = remove_constructors constructors in
      lambda_let (T.Lam (T.NoSelf, [], cps_match match_terms rest handle))
        (fun handle2 ->
           T.Switch (List.hd match_terms,
             List.map (fun (tag, (vars, patterns)) ->
               (tag, vars,
                cps_match (T.vvars vars @ List.tl match_terms)
                  patterns handle2
               )) cl,
             Some (T.TailCall (handle2, [])))
        )

let cps_term (t : S.term) : T.term =
  lambda_let (T.Lam (T.NoSelf, [Atom.fresh "cps_result"], T.Exit)) (cps t)
