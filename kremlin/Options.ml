(* By default, the C printer inserts a minimal amount of parentheses.
   However, this can trigger GCC and Clang's -Wparentheses warning,
   so there is an option to produce more parentheses than strictly
   necessary. *)

let parentheses =
  ref false
