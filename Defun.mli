(* Through defunctionalization, the intermediate language [Tail] is translated
   down to the next intermediate language, [Top]. *)

val defun_term: Tail.term -> Top.program
