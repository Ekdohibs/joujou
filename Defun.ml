(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

module IMap = Map.Make(struct type t = int let compare = compare end)

let gen_id =
  let c = ref 0 in fun () -> (incr c; !c - 1)

type defun_state = {
  mutable toplevel_functions : (Atom.atom * int) Atom.Map.t ;
  mutable extracted_functions : T.function_declaration list ;
  mutable apply_defs : (Atom.atom * Atom.atom list * T.branch list) IMap.t ;
}

let ( <|> ) a b =
  let rec aux a b r =
    if b <= a then r
    else aux a (b - 1) ((b - 1) :: r)
  in aux a b []

let get_apply_def (st : defun_state) (arity : int) =
  try
    IMap.find arity st.apply_defs
  with Not_found ->
    let v = Atom.fresh ("defun_apply_" ^ (string_of_int arity) ^ "_") in
    let args = List.map (fun _ -> Atom.fresh "defun_apply_var") (0 <|> arity) in
    st.apply_defs <- IMap.add arity (v, args, []) st.apply_defs;
    (v, args, [])

let rec defun_value (st : defun_state) (k : T.value -> T.term) (t : S.value) : T.term =
  match t with
  | S.VVar v ->
    if Atom.Map.mem v st.toplevel_functions then
      let nv = Atom.fresh "defun_toplevel_func" in
      T.LetBlo (nv, T.Con (snd (Atom.Map.find v st.toplevel_functions), []),
                k (T.VVar nv))
    else
      k t
  | S.VLit _ -> k t
  | S.VBinOp (t1, op, t2) ->
    defun_value st (fun t1 ->
        defun_value st (fun t2 ->
            k (T.VBinOp (t1, op, t2))) t2) t1

let rec defun_values (st : defun_state) (k : T.value list -> T.term) (l : S.value list) : T.term =
  match l with
  | [] -> k []
  | v :: ls -> defun_value st (fun v -> defun_values st (fun ls -> k (v :: ls)) ls) v

let rec defun (t : S.term) (st : defun_state) : T.term =
  match t with
  | S.Exit -> T.Exit
  | S.TailCall (S.VVar f, args) when Atom.Map.mem f st.toplevel_functions ->
    defun_values st (fun args ->
        T.TailCall (fst (Atom.Map.find f st.toplevel_functions), args)) args
  | S.TailCall (f, args) ->
    let arity = List.length args in
    let app, _, _ = get_apply_def st arity in
    defun_values st (fun args -> T.TailCall (app, args)) (f :: args)
  | S.ContCall (f, k, args) ->
    let arity = List.length args in
    defun (S.TailCall (f, (k :: args))) st
  | S.Print (v, t) -> defun_value st (fun v -> T.Print (v, defun t st)) v
  | S.LetVal (x, v, t) ->
    defun_value st (fun v -> T.LetVal (x, v, defun t st)) v
  | S.LetBlo (f, (S.Lam (self, args, body) as blo), t) ->
    let fv = Atom.Set.(elements
       (diff (S.fv_block blo) (Atom.Map.domain st.toplevel_functions))) in
    Format.eprintf "%a %d@." Atom.pp f (List.length fv);
    let fv1 = List.map Atom.copy fv in
    let ren = List.fold_left2 (fun m u v -> Atom.Map.add u v m) Atom.Map.empty fv fv1 in
    let fname = match self with
      | S.NoSelf -> Atom.fresh "defun_lambda"
      | S.Self f -> Atom.copy f
    in
    let tag = gen_id () in
    if fv = [] then begin
      st.toplevel_functions <- Atom.Map.add f (fname, tag) st.toplevel_functions;
      match self with
      | S.NoSelf -> ()
      | S.Self f -> st.toplevel_functions <- Atom.Map.add f (fname, tag) st.toplevel_functions
    end;
    let nbody = defun (S.rename_term ren body) st in
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
    let nt = defun t st in
    st.extracted_functions <- fdef :: st.extracted_functions;
    T.LetBlo (f, T.Con (tag, T.vvars fv), nt)
  | S.IfZero (v, t1, t2) ->
    defun_value st (fun v -> T.IfZero (v, defun t1 st, defun t2 st)) v

let defun_term (t : S.term) : T.program =
  let st = {
    toplevel_functions = Atom.Map.empty ;
    extracted_functions = [] ;
    apply_defs = IMap.empty ;
  } in
  let nt = defun t st in
  let applies = List.map (fun (_, (name, args, branches)) ->
      let f = Atom.fresh "apply_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, branches))
    ) (IMap.bindings st.apply_defs) in
  T.Prog (applies @ st.extracted_functions, nt)
