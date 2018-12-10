(* Through defunctionalization, the intermediate language [Tail] is translated
   down to the next intermediate language, [Apply]. *)

val defun_term: Tail.term -> Apply.program
