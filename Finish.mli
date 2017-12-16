(* This function implements a translation of the intermediate language [Top]
   down to [C]. This transformation is mostly a matter of choosing appropriate
   C constructs to reflect the concepts of the language [Top]. *)

val finish_program: Top.program -> C.program
