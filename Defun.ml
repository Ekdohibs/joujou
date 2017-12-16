(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

module IMap = Map.Make(struct type t = int let compare = compare end)

let gen_id =
  let c = ref 0 in fun () -> (incr c; !c - 1)

type defun_state = T.function_declaration list *
                   ((Atom.atom * Atom.atom list * T.branch list) IMap.t)

let ( <|> ) a b =
  let rec aux a b r =
    if b <= a then r
    else aux a (b - 1) ((b - 1) :: r)
  in aux a b []

let get_apply apply arity =
  try IMap.find arity apply, apply
  with Not_found ->
    let v = Atom.fresh ("defun_apply_" ^ (string_of_int arity) ^ "_") in
    let args = List.map (fun _ -> Atom.fresh "defun_apply_var") (0 <|> arity) in
    (v, args, []), IMap.add arity (v, args, []) apply

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

let rec defun (t : S.term) (st : defun_state) : (defun_state * T.term) =
  match t with
  | S.Exit -> (st, T.Exit)
  | S.TailCall (f, args) ->
    let fcts, apply = st in
    let arity = List.length args in
    let (app, _, _), apply = get_apply apply arity in
    ((fcts, apply), T.TailCall (app, (f :: args)))
  | S.Print (v, t) ->
    let st, nt = defun t st in
    (st, T.Print (v, nt))
  | S.LetVal (x, v, t) ->
    let st, nt = defun t st in
    (st, T.LetVal (x, v, nt))
  | S.LetBlo (f, (S.Lam (self, args, body) as blo), t) ->
    let fv = Atom.Set.elements (S.fv_block blo) in
    let fv1 = List.map Atom.copy fv in
    let ren = List.fold_left2 (fun m u v -> Atom.Map.add u v m) Atom.Map.empty fv fv1 in
    let st, nbody = defun (S.rename_term ren body) st in
    let st, nt = defun t st in
    let fcts, apply = st in
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
    let (app, aargs, branches), apply = get_apply apply arity in
    let fv2 = List.map Atom.copy fv in
    let branch = T.Branch (tag, fv2, T.TailCall (fname, T.vvars (aargs @ fv2))) in
    let apply = IMap.add arity (app, aargs, branch :: branches) apply in
    let fcts = fdef :: fcts in
    ((fcts, apply), T.LetBlo (f, T.Con (tag, T.vvars fv), nt))

let defun_term (t : S.term) : T.program =
  let (fcts, apply), nt = defun (simpl t) ([], IMap.empty) in
  let applies = List.map (fun (_, (name, args, branches)) ->
      let f = Atom.fresh "apply_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, branches))
    ) (IMap.bindings apply) in
  T.Prog (applies @ fcts, nt)
