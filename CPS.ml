(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

let block_let (blo : T.block) (body : T.value -> T.term) : T.term =
  let f = Atom.fresh "cps_block_let" in
  T.LetBlo (f, blo, body (T.vvar f))

let make_handler (body : T.value -> T.value -> T.value -> T.term) : T.block =
  let handle_var = Atom.fresh "cps_handler_var" in
  let handle_res = Atom.fresh "cps_handler_res" in
  let handle_ks = Atom.fresh "cps_handler_ks" in
  T.Lam (T.NoSelf, [handle_var; handle_res; handle_ks],
        body (T.vvar handle_var) (T.vvar handle_res) (T.vvar handle_ks))

let make_statichandler (body : T.term) : T.block =
  T.Lam (T.NoSelf, [], body)

let dynamic_destruct_cons (ks : T.value) (body : T.value -> T.value -> T.term) : T.term =
  let hd = Atom.fresh "cps_ks_hd" in
  let tl = Atom.fresh "cps_ks_tl" in
  T.DestructTuple (ks, [hd; tl], body (T.vvar hd) (T.vvar tl))

let lift (x : T.value) (body : T.value -> T.term) : T.term =
  body x

type static_list =
  | Static_cons of ((T.value -> T.term) -> T.term) * static_list
  | Reflect of ((T.value -> T.term) -> T.term)

let cont_let (f : T.block) (ks : static_list) (body : static_list -> T.term) : T.term =
  body (Static_cons (block_let f, ks))

let rec reify (vs : static_list) (body : T.value -> T.term) : T.term =
  match vs with
  | Static_cons (v, vs) ->
    v (fun v -> reify vs (fun vs -> block_let (T.Tuple [v; vs]) body))
  | Reflect v -> v body

let make_cont (body : T.value -> static_list -> T.term) : T.block =
  let cont_var = Atom.fresh "cps_cont_var" in
  let cont_ks = Atom.fresh "cps_cont_ks" in
  T.Lam (T.NoSelf, [cont_var; cont_ks], body (T.vvar cont_var) (Reflect (lift (T.vvar cont_ks))))

let destruct_cons (ks : static_list) (body : T.value -> static_list -> T.term) : T.term =
  match ks with
  | Static_cons (k, ks) ->
    k (fun k -> body k ks)
  | Reflect ks ->
    ks (fun ks -> dynamic_destruct_cons ks (fun k ks -> body k (Reflect (lift ks))))

let apply_cont_p (k : T.value) (ks : static_list) (t : T.value) : T.term =
  reify ks (fun ks -> T.TailCall (k, [t; ks]))

let apply_cont (ks : static_list) (t : T.value) : T.term =
  destruct_cons ks (fun k ks -> apply_cont_p k ks t)

let rec cps (t : S.term) (ks : static_list) : T.term =
  match t with
  | S.Var v -> apply_cont ks (T.vvar v)
  | S.Lit n -> apply_cont ks (T.VLit n)
  | S.Lam (self, var, body) ->
    let conts = Atom.fresh "cps_conts" in
    let args, body1 = cps_lam body [var] in
    block_let (T.Lam (self, List.rev (conts :: args),
                      cps body1 (Reflect (lift (T.vvar conts)))))
      (apply_cont ks)
  | S.App (_, _) ->
    destruct_cons ks (fun k ks ->
      cps_app t k ks [])
  | S.BinOp (t1, op, t2) ->
    destruct_cons ks (fun k ks ->
      cont_let (make_cont (fun bl ks ->
        cont_let (make_cont (fun br ks ->
          apply_cont_p k ks (T.VBinOp (bl, op, br))
        )) ks (cps t2)
      )) ks (cps t1))
  | S.Print t ->
    destruct_cons ks (fun k ks ->
      cont_let (make_cont (fun pr ks ->
        T.Print (pr, apply_cont_p k ks pr)
      )) ks (cps t))
  | S.Let (x, t1, t2) ->
    let cks = Atom.fresh "cps_cont_ks" in
    destruct_cons ks (fun k ks ->
      cont_let
        (T.Lam (T.NoSelf, [x; cks],
                cps t2 (Static_cons (lift k, Reflect (lift (T.vvar cks))))))
        ks (cps t1))
  | S.IfZero (t1, t2, t3) ->
    destruct_cons ks (fun k ks ->
      cont_let (make_cont (fun cond ks ->
        T.IfZero (cond,
                  cps t2 (Static_cons (lift k, ks)),
                  cps t3 (Static_cons (lift k, ks)))
      )) ks (cps t1))
  | S.Match (t, pl) ->
    let patterns, effects = List.partition
        (function (S.Pattern _, _) -> true | (S.Effect _, _) -> false) pl in
    let patterns = List.map
        (function (S.Pattern p, t) -> (p, t) | _ -> assert false) patterns in
    let effects = List.map
        (function (S.Effect (p, k), t) -> (p, k, t) | _ -> assert false) effects in
    let do_match v ks =
      let match_failure = make_statichandler T.Exit in
      block_let match_failure (fun handle ->
        cps_match [v] (List.map (fun (p, t) ->
          [p], (cps t ks))
          patterns) handle
      )
    in
    if effects = [] then
      cont_let (make_cont do_match) ks (cps t)
    else
      let hret = make_cont (fun v ks -> destruct_cons ks (fun _ ks -> do_match v ks)) in
      let heffect = make_handler (fun e r ks ->
        let forward = dynamic_destruct_cons ks (fun k1 ks ->
          dynamic_destruct_cons ks (fun h1 ks ->
            block_let (make_cont (fun x ks ->
              reify (Static_cons (lift k1, Static_cons (lift h1, ks))) (fun ks ->
                T.TailCall (r, [x; ks])
              ))) (fun r1 ->
              T.TailCall (h1, [e; r1; ks])
            )
          )
        ) in
        block_let (make_statichandler forward) (fun handle ->
          cps_match [e] (List.map (fun (p, r1, t) ->
            [p], T.LetVal (r1, r, cps t (Reflect (lift ks)))) effects) handle
          )
        )
      in
      cps t (Static_cons (block_let hret, Static_cons (block_let heffect, ks)))
  | S.Tuple l ->
    destruct_cons ks (fun k ks ->
      let vars = List.map (fun _ -> Atom.fresh "cps_tuple_var") l in
      let finish = fun ks ->
        block_let (T.Tuple (T.vvars vars)) (apply_cont_p k ks)
      in
      List.fold_left2 (fun c t name ->
        let cks = Atom.fresh "cps_tuple_ks" in
        fun ks -> cont_let (T.Lam (T.NoSelf, [name; cks], c (Reflect (lift (T.vvar cks))))) ks (cps t)
      ) finish l vars ks)
  | S.Constructor ((_, tag, is_effect), l) ->
    destruct_cons ks (fun k ks ->
      let vars = List.map (fun _ -> Atom.fresh "cps_constructor_var") l in
      let finish = fun ks ->
        if is_effect then
          block_let (T.Constructor (tag, T.vvars vars)) (fun e ->
            destruct_cons ks (fun h ks ->
              block_let (make_cont (fun x ks ->
                apply_cont_p k (Static_cons (lift h, ks)) x
              )) (fun w -> reify ks (fun ks -> T.TailCall (h, [e; w; ks])))
            )
          )
        else
          block_let (T.Constructor (tag, T.vvars vars)) (apply_cont_p k ks)
      in
      List.fold_left2 (fun c t name ->
        let cks = Atom.fresh "cps_contructor_ks" in
        fun ks -> cont_let (T.Lam (T.NoSelf, [name; cks], c (Reflect (lift (T.vvar cks))))) ks (cps t)
      ) finish l vars ks)

and cps_app (t : S.term) (k : T.value) (ks : static_list) (args : T.value list) : T.term =
  match t with
  | S.App (t1, t2) ->
    cont_let (make_cont (fun appr ks ->
      cps_app t1 k ks (appr :: args)
    )) ks (cps t2)
  | _ ->
    cont_let (make_cont (fun appl ks ->
        reify (Static_cons (lift k, ks)) (fun ks -> T.ContCall (appl, ks, args))))
      ks (cps t)

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
      | S.PConstructor ((_, tag, _), l1) :: l2, t ->
        let vars, patterns =
          try Hashtbl.find tbl tag
          with Not_found ->
            List.map (fun _ -> Atom.fresh "match_destruct_var") l1, []
        in
        Hashtbl.replace tbl tag (vars, (l1 @ l2, t) :: patterns)
      | _ -> assert false
    ) (List.rev matching);
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
      block_let (T.Lam (T.NoSelf, [], cps_match match_terms rest handle))
        (fun handle2 ->
           T.DestructTuple (List.hd match_terms, tvars,
             cps_match (T.vvars tvars @ List.tl match_terms)
               (flatten_tuples tuples) handle2
           )
        )
    | S.PVar _ :: _ ->
      let vars, rest = split_matching matching in
      block_let (T.Lam (T.NoSelf, [], cps_match match_terms rest handle))
        (fun handle2 ->
           cps_match (List.tl match_terms)
             (remove_top_vars vars (List.hd match_terms)) handle2
        )
    | S.PConstructor _ :: _ ->
      let constructors, rest = split_matching matching in
      let cl = remove_constructors constructors in
      block_let (T.Lam (T.NoSelf, [], cps_match match_terms rest handle))
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
  let finish = T.Lam (T.NoSelf, [Atom.fresh "cps_result_x"; Atom.fresh "cps_result_ks"], T.Exit) in
  let effect_finish = T.Lam (T.NoSelf, [Atom.fresh "cps_effect_e"; Atom.fresh "cps_effect_ks"; Atom.fresh "cps_effect_r"], T.Exit) in
  cps t (Static_cons (block_let finish, Static_cons (block_let effect_finish, Reflect (lift (T.VLit 0)))))
