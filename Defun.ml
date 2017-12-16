(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

module IMap = Map.Make(struct type t = int let compare = compare end)

let gen_id =
  let c = ref 0 in fun () -> (incr c; !c - 1)

type defun_state = {
  mutable extracted_functions : T.function_declaration list ;
  mutable apply_defs : (Atom.atom * Atom.atom list * T.branch list) IMap.t ;
}

let ( <|> ) a b =
  let rec aux a b r =
    if b <= a then r
    else aux a (b - 1) ((b - 1) :: r)
  in aux a b []

let rec simpl (t : S.term) : S.term =
  match t with
  | S.Exit | S.TailCall _ | S.Print _ -> t
  | S.LetVal (x, v, t) -> S.LetVal (x, v, simpl t)
  | S.LetBlo (f, S.Lam (self, args, body), t) ->
    let t = simpl t in
    let body = simpl body in
    begin match t with
      | S.TailCall (S.VVar f1, vals) when Atom.equal f f1 && self = S.NoSelf ->
        S.parallel_let args vals body
      | _ -> S.LetBlo (f, S.Lam (self, args, body), t)
    end
  | S.IfZero (v, t1, t2) -> S.IfZero (v, simpl t1, simpl t2)

let get_apply_def (st : defun_state) (arity : int) =
  try
    IMap.find arity st.apply_defs
  with Not_found ->
    let v = Atom.fresh ("defun_apply_" ^ (string_of_int arity) ^ "_") in
    let args = List.map (fun _ -> Atom.fresh "defun_apply_var") (0 <|> arity) in
    st.apply_defs <- IMap.add arity (v, args, []) st.apply_defs;
    (v, args, [])

let rec defun (t : S.term) (st : defun_state) : T.term =
  match t with
  | S.Exit -> T.Exit
  | S.TailCall (f, args) ->
    let arity = List.length args in
    let app, _, _ = get_apply_def st arity in
    T.TailCall (app, (f :: args))
  | S.Print (v, t) -> T.Print (v, defun t st)
  | S.LetVal (x, v, t) -> T.LetVal (x, v, defun t st)
  | S.LetBlo (f, (S.Lam (self, args, body) as blo), t) ->
    let fv = Atom.Set.elements (S.fv_block blo) in
    let fv1 = List.map Atom.copy fv in
    let ren = List.fold_left2 (fun m u v -> Atom.Map.add u v m) Atom.Map.empty fv fv1 in
    let nbody = defun (S.rename_term ren body) st in
    let nt = defun t st in
    let tag = gen_id () in
    let fname = match self with
      | S.NoSelf -> Atom.fresh "defun_lambda"
      | S.Self f -> Atom.copy f
    in
    let nbody = match self with
      | S.NoSelf -> nbody
      | S.Self f -> T.LetBlo (f, T.Con (tag, T.vvars fv1), nbody)
    in
    let fdef = T.Fun (fname, args @ fv1, nbody) in
    let arity = List.length args in
    let app, aargs, branches = get_apply_def st arity in
    let fv2 = List.map Atom.copy fv in
    let branch = T.Branch (tag, fv2, T.TailCall (fname, T.vvars (aargs @ fv2))) in
    st.apply_defs <- IMap.add arity (app, aargs, branch :: branches) st.apply_defs;
    st.extracted_functions <- fdef :: st.extracted_functions;
    T.LetBlo (f, T.Con (tag, T.vvars fv), nt)
  | S.IfZero (v, t1, t2) -> T.IfZero (v, defun t1 st, defun t2 st)

let defun_term (t : S.term) : T.program =
  let st = { extracted_functions = []; apply_defs = IMap.empty } in
  let nt = defun (simpl t) st in
  let applies = List.map (fun (_, (name, args, branches)) ->
      let f = Atom.fresh "apply_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, branches))
    ) (IMap.bindings st.apply_defs) in
  T.Prog (applies @ st.extracted_functions, nt)
