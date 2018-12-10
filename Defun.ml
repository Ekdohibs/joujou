(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Apply

module IMap = Map.Make(struct type t = int let compare = compare end)

type defun_state = {
  mutable toplevel_functions : (Atom.atom * int) Atom.Map.t ;
  (* Maps function name to arity, tag, name, and free variables *)
  mutable functions_tags : (int * int * Atom.atom * Atom.atom list) Atom.Map.t ;
  mutable extracted_functions : T.function_declaration Atom.Map.t ;
}

let ( <|> ) a b =
  let rec aux a b r =
    if b <= a then r
    else aux a (b - 1) ((b - 1) :: r)
  in aux a b []

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

let rec precompute (t : S.term) (st : defun_state) : unit =
  match t with
  | S.Exit | S.TailCall _ | S.ContCall _ -> ()
  | S.Print (_, t) | S.LetVal (_, _, t) | S.DestructTuple (_, _, t) ->
    precompute t st
  | S.IfZero (_, t1, t2) ->
    precompute t1 st;
    precompute t2 st
  | S.Switch (_, l, t) ->
    (match t with None -> () | Some t -> precompute t st);
    List.iter (fun (_, _, t) -> precompute t st) l
  | S.LetBlo (f, (S.Lam (self, args, body) as blo), t) ->
    let fv = Atom.Set.(elements
       (diff (S.fv_block blo) (Atom.Map.domain st.toplevel_functions))) in
    let arity = List.length args in
    let tag = T.gen_tag () in
    let ff = match self with S.NoSelf -> [f] | S.Self f1 -> [f; f1] in
    let fname =
      match self with S.NoSelf -> Atom.copy f | S.Self f1 -> Atom.copy f1 in
    List.iter (fun f ->
        st.functions_tags <-
          Atom.Map.add f (arity, tag, fname, fv) st.functions_tags) ff;
    if fv = [] then
      List.iter (fun f ->
          st.toplevel_functions <-
            Atom.Map.add f (fname, tag) st.toplevel_functions) ff;
    precompute t st;
    precompute body st
  | S.LetBlo (_, _, t) ->
    precompute t st

let split_args l k =
  let rec spl l k =
    if k = 0 then ([], l)
    else match l with
      | [] -> assert false
      | x :: ls -> let a, b = spl ls (k - 1) in (x :: a, b)
  in
  spl l k

let rec split_last l =
  match l with
  | [] -> assert false
  | [x] -> (x, [])
  | x :: ls -> let a, b = split_last ls in a, x :: b

let destruct_tuple v xs t =
  T.Swi (v, [T.Branch (0, xs, t)], None)

let rec defun (t : S.term) (st : defun_state) : T.term =
  match t with
  | S.Exit -> T.Exit
  | S.TailCall (f, args) ->
    defun_value st (fun f -> defun_values st (fun args -> T.TailCall (f, args)) args) f
  | S.ContCall (f, ks, args) ->
    defun_value st (fun f ->
        defun_value st (fun ks ->
            defun_values st (fun args -> T.ContCall (f, ks, args)) args
          ) ks
      ) f
  | S.Print (v, t) -> defun_value st (fun v -> T.Print (v, defun t st)) v
  | S.LetVal (x, v, t) ->
    defun_value st (fun v -> T.LetVal (x, v, defun t st)) v
  | S.LetBlo (f, (S.Lam (self, args, body) as blo), t) ->
    let _, tag, name, _ = Atom.Map.find f st.functions_tags in
    let fv = Atom.Set.(elements
       (diff (S.fv_block blo) (Atom.Map.domain st.toplevel_functions))) in
    let fv1 = List.map Atom.copy fv in
    let ren = List.fold_left2 (fun m u v -> Atom.Map.add u v m) Atom.Map.empty fv fv1 in
    let nbody = defun (S.rename_term ren body) st in
    let nbody = match self with
      | S.NoSelf -> nbody
      | S.Self f -> T.LetBlo (f, T.Con (tag, T.vvars fv1), nbody)
    in
    let fdef = T.Fun (name, tag, fv1, args, nbody) in
    let nt = defun t st in
    st.extracted_functions <- Atom.Map.add f fdef st.extracted_functions;
    T.LetBlo (f, T.Con (tag, T.vvars fv), nt)
  | S.LetBlo (x, S.Tuple l, t) ->
    defun_values st (fun l -> T.LetBlo (x, T.Con (0, l), defun t st)) l
  | S.LetBlo (x, S.Constructor (tag, l), t) ->
    defun_values st (fun l -> T.LetBlo (x, T.Con (tag, l), defun t st)) l
  | S.DestructTuple (v, xs, t) ->
    defun_value st (fun v -> T.Swi (v, [T.Branch (0, xs, defun t st)], None)) v
  | S.Switch (v, l, t) ->
    let t = match t with None -> None | Some t -> Some (defun t st) in
    defun_value st (fun v ->
        T.Swi (v, List.map (fun (tag, xs, t) ->
            T.Branch (tag, xs, defun t st)) l, t)) v
  | S.IfZero (v, t1, t2) ->
    defun_value st (fun v -> T.IfZero (v, defun t1 st, defun t2 st)) v

let defun_term (t : S.term) : T.program =
  let st = {
    toplevel_functions = Atom.Map.empty ;
    functions_tags = Atom.Map.empty ;
    extracted_functions = Atom.Map.empty ;
  } in
  (* Atom.Map.iter (fun z _ -> Format.eprintf "%s " (S.show_variable z)) st.functions_tags;
     Format.eprintf "@."; *)
  precompute t st;
  let nt = defun t st in
  T.Prog (List.map snd (Atom.Map.bindings st.extracted_functions), nt)
