(* The source calculus. *)
module S = Apply
(* The target calculus. *)
module T = Top

module IMap = Map.Make(struct type t = int let compare = compare end)

type dispatch_funcs = {
  (* Maps arity to the name and the names of the arguments of the
     application function for that arity *)
  mutable apply_defs : (Atom.atom * Atom.atom list) IMap.t ;
  (* Maps arity to the name, the names of the arguments and the tag of the
     continuation application function for that arity (including
     the continuation argument, so the length of the list is arity + 1). *)
  mutable cont_defs : (Atom.atom * Atom.atom list * int) IMap.t ;
}

let ( <|> ) a b =
  let rec aux a b r =
    if b <= a then r
    else aux a (b - 1) ((b - 1) :: r)
  in aux a b []

let get_apply_def (df : dispatch_funcs) (arity : int) =
  try
    IMap.find arity df.apply_defs
  with Not_found ->
    let v = Atom.fresh ("defun_apply_" ^ (string_of_int arity) ^ "_") in
    let args = List.map (fun _ -> Atom.fresh "defun_apply_var") (0 <|> arity) in
    df.apply_defs <- IMap.add arity (v, args) df.apply_defs;
    (v, args)

let get_cont_def (df : dispatch_funcs) (arity : int) =
  try
    IMap.find arity df.cont_defs
  with Not_found ->
    let v = Atom.fresh ("defun_cont_" ^ (string_of_int arity) ^ "_") in
    let args =
      List.map (fun _ -> Atom.fresh "defun_cont_var") (0 <|> arity) @ [Atom.fresh "defun_cont_ks"] in
    let tag = S.gen_tag () in
    df.cont_defs <- IMap.add arity (v, args, tag) df.cont_defs;
    (v, args, tag)

(*
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
*)

let rec get_max_contcall_arity (t : S.term) : int =
  match t with
  | S.Exit | S.TailCall _ -> -1
  | S.ContCall (_, _, args) -> List.length args
  | S.Print (_, t) | S.LetVal (_, _, t) -> get_max_contcall_arity t
  | S.IfZero (_, t1, t2) ->
    max (get_max_contcall_arity t1) (get_max_contcall_arity t2)
  | S.Swi (_, l, t) ->
    let mx = match t with None -> -1 | Some t -> get_max_contcall_arity t in
    List.fold_left (fun mx (S.Branch (_, _, t)) -> max mx (get_max_contcall_arity t)) mx l
  | S.LetBlo (_, _, t) ->
    get_max_contcall_arity t

let program_max_contcall_arity (t : S.program) : int =
  match t with
  | S.Prog (funs, t) ->
    List.fold_left (fun mx (S.Fun (_, _, _, _, body)) -> max mx (get_max_contcall_arity body))
      (get_max_contcall_arity t) funs

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

let rec split_last2 l =
  match l with
  | [] | [_] -> assert false
  | [x; y] -> ((x, y), [])
  | x :: ls -> let a, b = split_last2 ls in a, x :: b


let destruct_tuple v xs t =
  T.Swi (v, [T.Branch (0, xs, t)], None)

let rec dispatch (t : S.term) (df : dispatch_funcs) : T.term =
  match t with
  | S.Exit -> T.Exit
(*  | S.TailCall (S.VVar f, args) when Atom.Map.mem f st.toplevel_functions ->
    defun_values st (fun args ->
        T.TailCall (fst (Atom.Map.find f st.toplevel_functions), args)) args *)
  | S.TailCall (f, args) ->
    let arity = List.length args in
    let app, _ = get_apply_def df arity in
    T.TailCall (app, f :: args)
  | S.ContCall (f, ks, args) ->
    let arity = List.length args in
    let cont, _, _ = get_cont_def df arity in
    T.TailCall (cont, f :: args @ [ks])
  | S.Print (v, t) -> T.Print (v, dispatch t df)
  | S.LetVal (x, v, t) -> T.LetVal (x, v, dispatch t df)
  | S.LetBlo (c, blo, t) -> T.LetBlo (c, blo, dispatch t df)
  | S.IfZero (v, t1, t2) ->
    T.IfZero (v, dispatch t1 df, dispatch t2 df)
  | S.Swi (v, l, t) ->
    let t = match t with None -> None | Some t -> Some (dispatch t df) in
    T.Swi (v, List.map (fun (S.Branch (tag, xs, t)) ->
        T.Branch (tag, xs, dispatch t df)) l, t)

let dispatch_fundecl (f : S.function_declaration) (df : dispatch_funcs) : T.function_declaration =
  match f with
  | S.Fun (name, _, fv, args, body) -> T.Fun (name, fv @ args, dispatch body df)


let make_contcall (f : S.function_declaration) (tags : T.tag array)
    (already_applied : int) (ks : T.value)
    (args : T.value list) (extra : T.value list) (df : dispatch_funcs) : T.term =
  let S.Fun (name, _, fv, fargs, _) = f in
  let arity = List.length fargs in
  assert (Array.length tags = arity);
  assert (List.length fv + already_applied = List.length extra);
  let n = List.length args + already_applied in
  if n = arity - 1 then
    T.TailCall (name, extra @ args @ [ks])
  else if n < arity - 1 then
    let blo_name = Atom.fresh "cont_call_few_f" in
    let k = Atom.fresh "cont_call_few_k" in
    let ks1 = Atom.fresh "cont_call_few_ks1" in
    let ap, _ = get_apply_def df 2 in
    destruct_tuple ks [k; ks1]
      (T.LetBlo (blo_name, T.Con (tags.(n), extra @ args),
                 T.TailCall (ap, T.vvar k :: [T.vvar blo_name; T.vvar ks1])))
  else
    let argsa, argsb = split_args args ((arity - 1) - already_applied) in
    let blo_name = Atom.fresh "cont_call_many_f" in
    let k = Atom.fresh "cont_call_many_k" in
    let ks1 = Atom.fresh "cont_call_many_ks1" in
    let t_name = Atom.fresh "cont_call_many_t" in
    let _, _, cont_tag = get_cont_def df (n - (arity - 1)) in
    destruct_tuple ks [k; ks1]
      (T.LetBlo (blo_name, T.Con (cont_tag, argsb @ [T.vvar k]),
         T.LetBlo (t_name, T.Con (0, [T.vvar blo_name; T.vvar ks1]),
          T.TailCall (name, extra @ argsa @ [T.vvar t_name]))))


let dispatch_program (t : S.program) : T.program =
  let max_arity = program_max_contcall_arity t in
  let df = { apply_defs = IMap.empty ; cont_defs = IMap.empty } in
  let S.Prog (decls, t) = t in
  let ndecls = List.map (fun f -> dispatch_fundecl f df) decls in
  let nt = dispatch t df in
  let apply_branches = Array.make 4 [] in
  let cont_branches = Array.make (max_arity + 1) [] in
  let add_cont_branches f =
    let S.Fun (name, tag, fv, fargs, _) = f in
    let arity = List.length fargs in
    if arity >= 2 then begin
      let tags = Array.init arity (fun i -> if i = 0 then tag else S.gen_tag ()) in
      for i = 1 to max_arity do
        let _, cargs, _ = get_cont_def df i in
        let ks, aargs = split_last cargs in
        for j = 0 to arity - 2 do
          let fv1 = List.map Atom.copy fv in
          let extra = fv1 @
            (List.map (fun _ -> Atom.fresh "defun_cont_extra") (0 <|> j)) in
          cont_branches.(i) <-
            T.Branch (tags.(j), extra,
                      make_contcall f tags j (T.vvar ks)
                        (T.vvars aargs) (T.vvars extra) df)
            :: cont_branches.(i)
        done
      done
    end
  in
  let add_apply_branches f =
    let S.Fun (name, tag, fv, fargs, _) = f in
    let arity = List.length fargs in
    if arity <= 3 then begin
      let fv2 = List.map Atom.copy fv in
      let _, aargs = get_apply_def df arity in
      apply_branches.(arity) <-
        T.Branch (tag, fv2, T.TailCall (name, T.vvars (fv2 @ aargs)))
          :: apply_branches.(arity)
    end
  in
  List.iter (fun f -> add_cont_branches f; add_apply_branches f) decls;
  for i = 1 to max_arity do
    let _, aargs = get_apply_def df 2 in
    let f, ks = match aargs with [f; ks] -> (f, ks) | _ -> assert false in
    let cname, cargs, tag = get_cont_def df i in
    let cargs1 = List.map Atom.copy cargs in
    let k, cargs2 = split_last cargs1 in
    let t_name = Atom.fresh "cont_call_many_t" in
    apply_branches.(2) <-
      T.Branch (tag, cargs1,
        T.LetBlo (t_name, T.Con (0, T.vvars [k; ks]),
          T.TailCall (cname, T.vvars (f :: cargs2 @ [t_name]))))
        :: apply_branches.(2)
  done;
  let applies = List.map (fun (arity, (name, args)) ->
      let f = Atom.fresh "apply_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, apply_branches.(arity), None))
    ) (IMap.bindings df.apply_defs) in
  let conts = List.map (fun (arity, (name, args, _)) ->
      let f = Atom.fresh "cont_f" in
      T.Fun (name, f :: args, T.Swi (T.vvar f, cont_branches.(arity), None))
    ) (IMap.bindings df.cont_defs) in
  T.Prog (conts @ applies @ ndecls, nt)
