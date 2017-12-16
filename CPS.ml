(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

let lambda_let (lam : T.block) (body : T.value -> T.term) : T.term =
  let f = Atom.fresh "cps_lambda_let" in
  T.LetBlo (f, lam, body (T.vvar f))

let rec cps (t : S.term) (k : T.value) : T.term =
  match t with
  | S.Var v -> T.TailCall (k, [T.vvar v])
  | S.Lam (self, var, body) ->
    let cont = Atom.fresh "cps_cont" in
    lambda_let (T.Lam (self, [var; cont], cps body (T.vvar cont)))
      (fun f -> T.TailCall (k, [f]))
  | S.App (t1, t2) ->
    let appl = Atom.fresh "cps_appl" in
    let appr = Atom.fresh "cps_appr" in
    let w =
      lambda_let (T.Lam (T.NoSelf, [appr],
                         T.TailCall (T.vvar appl, [T.vvar appr; k])))
        (cps t2) in
    lambda_let (T.Lam (T.NoSelf, [appl], w)) (cps t1)
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
  | S.Let (x, t1, t2) ->
    lambda_let (T.Lam (T.NoSelf, [x], cps t2 k)) (cps t1)
  | S.IfZero (t1, t2, t3) ->
    let cond = Atom.fresh "cps_if" in
    lambda_let (T.Lam (T.NoSelf, [cond],
                       T.IfZero (T.vvar cond, cps t2 k, cps t3 k))) (cps t1)

let cps_term (t : S.term) : T.term =
  lambda_let (T.Lam (T.NoSelf, [Atom.fresh "cps_result"], T.Exit)) (cps t)
