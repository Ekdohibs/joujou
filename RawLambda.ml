(* Variables are strings. *)

type variable =
  string
and constructor =
  string

(* Every [let] binding is marked recursive or nonrecursive. *)

and recursive =
  | Recursive
  | NonRecursive

(* The four standard integer arithmetic operations are supported. *)

and binop =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv

(* This language is the untyped lambda-calculus, extended with possibly
   recursive [let] bindings, integer literals (that is, constants), integer
   arithmetic operations, and the primitive operation [print], which prints an
   integer value and returns it. *)

and term_ =
  | Var of variable
  | Lam of variable * term
  | App of term * term
  | Lit of int
  | BinOp of term * binop * term
  | Print of term
  | Let of recursive * variable * term * term
  | IfZero of term * term * term
  | CallCc of term
  | Match of term * (pattern_or_effect * term) list
  | Tuple of term list
  | Constructor of constructor * term option

(* Every abstract syntax tree node of type [term] is annotated with a place,
   that is, a position in the source code. This allows us to produce a good
   error message when a problem is detected. *)

and term =
  term_ placed

and pattern_ =
  | PVar of variable
  | PConstructor of constructor * pattern option
  | POr of pattern * pattern
  | PTuple of pattern list

and pattern =
  pattern_ placed

and pattern_or_effect =
  | Pattern of pattern
  | Effect of constructor * pattern option * variable

and ty_ =
  | TVar of variable
  | TTuple of ty list
  | TArrow of ty * ty

and ty =
  ty_ placed

and decl_ =
  | DLet of recursive * variable * term
  | DNewType of variable * (constructor * ty list) placed list
  | DEffect of variable * (constructor * ty option * ty) placed list
  | DTypeSynonym of variable * ty
  | DTerm of term

and decl =
  decl_ placed

and program =
  decl list

(* A value of type ['a placed] can be thought of as a value of type ['a]
   decorated with a place. *)

and 'a placed = {
  place: Error.place;
  value: 'a
  }

(* The following annotation requests the automatic generation of a [show_]
   function for each of the types defined above. For instance, the function
   [show_term], of type [term -> string], converts a term to a string. These
   functions can be useful during debugging. Running with [--debug] causes
   every intermediate abstract syntax tree to be displayed in this way. *)

[@@deriving show { with_path = false }]
