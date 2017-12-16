(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

let cps_term (t : S.term) : T.term =
  assert false
