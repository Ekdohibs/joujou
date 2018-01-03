(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

module IMap = Map.Make(struct type t = int let compare = compare end)

let gen_id =
  let c = ref 0 in fun () -> (incr c; !c - 1)

type defun_state = {
  mutable toplevel_functions : (Atom.atom * int) Atom.Map.t ;
  (* Maps function name to arity, tag when already applied to some
     number of arguments, name, and free variables *)
  mutable functions_tags : (int * int array * Atom.atom * Atom.atom list) Atom.Map.t ;
  mutable extracted_functions : T.function_declaration Atom.Map.t ;
  (* Maps arity to the name and the names of the arguments of the
     application function for that arity *)
  mutable apply_defs : (Atom.atom * Atom.atom list) IMap.t ;
  (* Maps arity to the name, the names of the arguments and the tag of the
     continuation application function for that arity (including
     the continuation argument, so the length of the list is arity + 1). *)
  mutable cont_defs : (Atom.atom * Atom.atom list * int) IMap.t ;
  mutable max_contcall_arity : int ;
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
    st.apply_defs <- IMap.add arity (v, args) st.apply_defs;
    (v, args)

let get_cont_def (st : defun_state) (arity : int) =
  try
    IMap.find arity st.cont_defs
  with Not_found ->
    let v = Atom.fresh ("defun_cont_" ^ (string_of_int arity) ^ "_") in
    let args =
      List.map (fun _ -> Atom.fresh "defun_cont_var") (0 <|> arity) @ [Atom.fresh "defun_cont_f"; Atom.fresh "defun_cont_h"] in
    let tag = gen_id () in
    st.cont_defs <- IMap.add arity (v, args, tag) st.cont_defs;
    (v, args, tag)


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
  | S.Exit | S.TailCall _ -> ()
  | S.ContCall (_, _, _, args) ->
    st.max_contcall_arity <- max st.max_contcall_arity (List.length args)
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
    let tags = Array.init (max 1 (arity - 2)) (fun _ -> gen_id ()) in
    let ff = match self with S.NoSelf -> [f] | S.Self f1 -> [f; f1] in
    let fname =
      match self with S.NoSelf -> Atom.copy f | S.Self f1 -> Atom.copy f1 in
    List.iter (fun f ->
        st.functions_tags <-
          Atom.Map.add f (arity, tags, fname, fv) st.functions_tags) ff;
    if fv = [] then
      List.iter (fun f ->
          st.toplevel_functions <-
            Atom.Map.add f (fname, tags.(0)) st.toplevel_functions) ff;
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

let make_contcall (fname : Atom.atom) (already_applied : int) (k : T.value) (h : T.value) (args : T.value list) (extra : T.value list) (st : defun_state) : T.term =
  let arity, tags, name, fv = Atom.Map.find fname st.functions_tags in
  assert (List.length fv + already_applied = List.length extra);
  let n = List.length args + already_applied in
  if n = arity - 2 then
    T.TailCall (name, extra @ args @ [k; h])
  else if n < arity - 2 then
    let blo_name = Atom.fresh "cont_call_few_f" in
    let ap, _ = get_apply_def st 1 in
    T.LetBlo (blo_name, T.Con (tags.(n), extra @ args),
              T.TailCall (ap, k :: [T.vvar blo_name]))
  else
    let argsa, argsb = split_args args ((arity - 2) - already_applied) in
    let blo_name = Atom.fresh "cont_call_many_f" in
    let _, _, cont_tag = get_cont_def st (n - (arity - 2)) in
    T.LetBlo (blo_name, T.Con (cont_tag, argsb @ [k; h]),
             T.TailCall (name, extra @ argsa @ [T.vvar blo_name; h]))


let rec defun (t : S.term) (st : defun_state) : T.term =
  match t with
  | S.Exit -> T.Exit
  | S.TailCall (S.VVar f, args) when Atom.Map.mem f st.toplevel_functions ->
    defun_values st (fun args ->
        T.TailCall (fst (Atom.Map.find f st.toplevel_functions), args)) args
  | S.TailCall (f, args) ->
    let arity = List.length args in
    let app, _ = get_apply_def st arity in
    defun_values st (fun args -> T.TailCall (app, args)) (f :: args)
  | S.ContCall (f, k, h, args) ->
    let arity = List.length args in
    let cont, _, _ = get_cont_def st arity in
    defun_values st (fun args -> T.TailCall (cont, args)) (f :: args @ [k; h])
  | S.Print (v, t) -> defun_value st (fun v -> T.Print (v, defun t st)) v
  | S.LetVal (x, v, t) ->
    defun_value st (fun v -> T.LetVal (x, v, defun t st)) v
  | S.LetBlo (f, (S.Lam (self, args, body) as blo), t) ->
    Format.eprintf "%s@." (S.show_variable f);
    let arity, tags, name, _ = Atom.Map.find f st.functions_tags in
    let fv = Atom.Set.(elements
       (diff (S.fv_block blo) (Atom.Map.domain st.toplevel_functions))) in
    let fv1 = List.map Atom.copy fv in
    let ren = List.fold_left2 (fun m u v -> Atom.Map.add u v m) Atom.Map.empty fv fv1 in
    let nbody = defun (S.rename_term ren body) st in
    let nbody = match self with
      | S.NoSelf -> nbody
      | S.Self f -> T.LetBlo (f, T.Con (tags.(0), T.vvars fv1), nbody)
    in
    let fdef = T.Fun (name, fv1 @ args, nbody) in
    let nt = defun t st in
    st.extracted_functions <- Atom.Map.add f fdef st.extracted_functions;
    T.LetBlo (f, T.Con (tags.(0), T.vvars fv), nt)
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
    apply_defs = IMap.empty ;
    cont_defs = IMap.empty ;
    max_contcall_arity = 0 ;
  } in
  Atom.Map.iter (fun z _ -> Format.eprintf "%s " (S.show_variable z)) st.functions_tags;
  Format.eprintf "@.";
  precompute t st;
  let max_arity = st.max_contcall_arity in
  let nt = defun t st in
  let apply_branches = Array.make 2 [] in
  let cont_branches = Array.make (max_arity + 1) [] in
  let add_cont_branches fname =
    let arity, tags, _, fv = Atom.Map.find fname st.functions_tags in
    if arity >= 3 then begin
      for i = 1 to st.max_contcall_arity do
        let _, cargs, _ = get_cont_def st i in
        let h, cargs1 = split_last cargs in
        let k, aargs = split_last cargs1 in
        for j = 0 to arity - 3 do
          let fv1 = List.map Atom.copy fv in
          let extra = fv1 @
            (List.map (fun _ -> Atom.fresh "defun_cont_extra") (0 <|> j)) in
          cont_branches.(i) <-
            T.Branch (tags.(j), extra,
                      make_contcall fname j (T.vvar k) (T.vvar h)
                        (T.vvars aargs) (T.vvars extra) st)
            :: cont_branches.(i)
        done
      done
    end
  in
  let add_apply_branches fname =
    let arity, tags, name, fv = Atom.Map.find fname st.functions_tags in
    if arity <= 1 then begin
      let fv2 = List.map Atom.copy fv in
      let _, aargs = get_apply_def st arity in
      apply_branches.(arity) <-
        T.Branch (tags.(0), fv2, T.TailCall (name, T.vvars (fv2 @ aargs)))
          :: apply_branches.(arity)
    end
  in
  Atom.Map.iter (fun fname _ -> add_cont_branches fname; add_apply_branches fname) st.extracted_functions;
  for i = 1 to st.max_contcall_arity do
    let _, aargs = get_apply_def st 1 in
    let cname, cargs, tag = get_cont_def st i in
    let cargs1 = List.map Atom.copy cargs in
    apply_branches.(1) <-
      T.Branch (tag, cargs1, T.TailCall (cname, T.vvars (aargs @ cargs1)))
        :: apply_branches.(1)
  done;
  let applies = List.map (fun (arity, (name, args)) ->
      let f = Atom.fresh "apply_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, apply_branches.(arity), None))
    ) (IMap.bindings st.apply_defs) in
  let conts = List.map (fun (arity, (name, args, _)) ->
      let f = Atom.fresh "cont_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, cont_branches.(arity), None))
    ) (IMap.bindings st.cont_defs) in
  T.Prog (conts @ applies @ (List.map (fun (_, f) -> f) (Atom.Map.bindings st.extracted_functions)), nt)
