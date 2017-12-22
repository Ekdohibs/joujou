(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

module IMap = Map.Make(struct type t = int let compare = compare end)

let gen_id =
  let c = ref 0 in fun () -> (incr c; !c - 1)

type defun_state = {
  mutable toplevel_functions : (Atom.atom * int) Atom.Map.t ;
  mutable extracted_functions : (T.function_declaration * int * Atom.atom list * int) list ;
  (* Maps arity to the name and the names of the arguments of the
     application function for that arity *)
  mutable apply_defs : (Atom.atom * Atom.atom list) IMap.t ;
  (* Maps arity to the name and the names of the arguments of the
     continuation application function for that arity (including
     the continuation argument, so the length of the list is arity + 1). *)
  mutable cont_defs : (Atom.atom * Atom.atom list) IMap.t ;
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
      List.map (fun _ -> Atom.fresh "defun_cont_var") (0 <|> arity) @ [Atom.fresh "defun_cont_f"] in
    st.cont_defs <- IMap.add arity (v, args) st.cont_defs;
    (v, args)


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
    let app, _ = get_apply_def st arity in
    defun_values st (fun args -> T.TailCall (app, args)) (f :: args)
  | S.ContCall (f, k, args) ->
(*    let arity = List.length args in
      defun (S.TailCall (f, (k :: args))) st *)
    let arity = List.length args in
    let cont, _ = get_cont_def st arity in
    defun_values st (fun args -> T.TailCall (cont, args)) (f :: args @ [k])
  | S.Print (v, t) -> defun_value st (fun v -> T.Print (v, defun t st)) v
  | S.LetVal (x, v, t) ->
    defun_value st (fun v -> T.LetVal (x, v, defun t st)) v
  | S.LetBlo (f, (S.Lam (self, args, body) as blo), t) ->
    let fv = Atom.Set.(elements
       (diff (S.fv_block blo) (Atom.Map.domain st.toplevel_functions))) in
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
    let fdef = (T.Fun (fname, fv1 @ args, nbody), tag, fv1, List.length args) in
    let nt = defun t st in
    st.extracted_functions <- fdef :: st.extracted_functions;
    T.LetBlo (f, T.Con (tag, T.vvars fv), nt)
  | S.IfZero (v, t1, t2) ->
    defun_value st (fun v -> T.IfZero (v, defun t1 st, defun t2 st)) v

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

let defun_term (t : S.term) : T.program =
  let st = {
    toplevel_functions = Atom.Map.empty ;
    extracted_functions = [] ;
    apply_defs = IMap.empty ;
    cont_defs = IMap.empty ;
  } in
  let nt = defun t st in
  let max_arity = List.fold_left max 0
      (List.map (fun (_, _, _, arity) -> arity) st.extracted_functions) in
  let max_arity = max max_arity
      (if IMap.is_empty st.apply_defs then 0 else
        (fst (IMap.max_binding st.apply_defs))) in
  let max_arity = max max_arity
      (if IMap.is_empty st.cont_defs then 0 else
         (fst (IMap.max_binding st.cont_defs))) in
  let apply_branches = Array.make (max_arity + 1) [] in
  let cont_branches = Array.make (max_arity + 1) [] in
  let cont_call_id = Array.init max_arity (fun _ -> gen_id ()) in
  let underapplied_tags = List.fold_left (fun m (_, tag, fv, arity) ->
      let tags = Array.init (arity - 1) (fun _ -> gen_id ()) in
      let v = (fv, tags) in
      Array.fold_left (fun m tag -> IMap.add tag v m) (IMap.add tag v m) tags)
      IMap.empty st.extracted_functions in
  let add_fct_branches name tag fv arity is_contcall =
    let fv2 = List.map Atom.copy fv in
    let _, aargs = get_apply_def st arity in
    if is_contcall then
      apply_branches.(arity) <-
        T.Branch (tag, fv2, T.TailCall (name, T.vvars (aargs @ fv2))) ::
        apply_branches.(arity)
    else
      apply_branches.(arity) <-
        T.Branch (tag, fv2, T.TailCall (name, T.vvars (fv2 @ aargs))) ::
        apply_branches.(arity);
    if arity > 1 then begin
      let _, cargs = get_cont_def st (arity - 1) in
      let fv3 = List.map Atom.copy fv in
      cont_branches.(arity - 1) <-
        T.Branch (tag, fv3, T.TailCall (name, T.vvars (fv3 @ cargs))) ::
        cont_branches.(arity - 1);
      for i = 2 to arity - 1 do
        let b_name = Atom.fresh "cont_call_few_f" in
        let _, nargs = get_cont_def st (i - 1) in
        let k, arga = split_last nargs in
        let ffv, tags = IMap.find tag underapplied_tags in
        let fv4 = List.map Atom.copy ffv in
        let oa = 1 + Array.length tags in
        let ntag = tags.(arity - 1 - i) in
        let argb = List.map (fun _ -> Atom.fresh "cont_call_few_arg") (0 <|> oa - arity) in
        let ap, _ = get_apply_def st 1 in
        cont_branches.(i - 1) <-
          T.Branch (tag, fv4 @ argb, T.LetBlo (
              b_name,
              T.Con (ntag, T.vvars (fv4 @ argb @ arga)),
              T.TailCall (ap, T.vvars [k; b_name])
            )) :: cont_branches.(i - 1)
      done;
      for i = arity + 1 to max_arity + 1 do
        let fv5 = List.map Atom.copy fv in
        let b_name = Atom.fresh "cont_call_many_f" in
        let _, nargs = get_cont_def st (i - 1) in
        let arga, argb = split_args nargs (arity - 1) in
        cont_branches.(i - 1) <-
          T.Branch (tag, fv5, T.LetBlo (
              b_name,
              T.Con (cont_call_id.(i - arity), T.vvars argb),
              T.TailCall (name, T.vvars (fv5 @ arga @ [b_name]))))
          :: cont_branches.(i - 1)
      done;
    end
  in
  List.iter (fun (T.Fun (name, _, _), tag, fv, arity) ->
      add_fct_branches name tag fv arity false;
      Array.iteri (fun i tag ->
          let nfv = List.map (fun _ -> Atom.fresh "cont_call_few_arg") (0 <|> arity - i - 2) in
          add_fct_branches name tag (fv @ nfv) (i + 2) false
        ) (snd (IMap.find tag underapplied_tags))
    ) st.extracted_functions;
  for i = 1 to max_arity - 1 do
    let vrs = List.map (fun _ -> Atom.fresh "cont_call_many") (0 <|> i + 1) in
    let name, _ = get_cont_def st i in
    add_fct_branches name cont_call_id.(i) vrs 1 true
  done;
  let applies = List.map (fun (arity, (name, args)) ->
      let f = Atom.fresh "apply_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, apply_branches.(arity)))
    ) (IMap.bindings st.apply_defs) in
  let conts = List.map (fun (arity, (name, args)) ->
      let f = Atom.fresh "cont_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, cont_branches.(arity)))
    ) (IMap.bindings st.cont_defs) in
  T.Prog (conts @ applies @ (List.map (fun (f, _, _, _) -> f) st.extracted_functions), nt)
