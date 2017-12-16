(* This module translates [RawLambda] into [Lambda]. *)

(* This involves ensuring that every name is properly bound (otherwise, an
   error is reported) and switching from a representation of names as strings
   to a representation of names as atoms. *)

(* This also involves checking that the right-hand side of every [let]
   construct is a function (otherwise, an error is reported) and switching
   from a representation where [let] constructs can carry a [rec] annotation
   to a representation where functions can carry such an annotation. *)

(* This also involves dropping places (that is, source code locations), since
   they are no longer used after this phase. *)

val cook_term: RawLambda.term -> Lambda.term
