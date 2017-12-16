(* Through a CPS transformation, the surface language [Lambda] is translated
   down to the intermediate language [Tail]. *)

val cps_term: Lambda.term -> Tail.term
