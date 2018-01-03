%token<string> IDENT
%token<string> UIDENT
%token<int> INTLITERAL
%token FUN IN LET PRINT REC CALLCC
%token IFZERO THEN ELSE
%token ARROW EQ LPAREN RPAREN BAR COMMA STAR SEMISEMI COLON
%token TYPE OF EFFECT
%token MATCH WITH
%token<RawLambda.binop> MULOP ADDOP
%token EOF

%nonassoc IN
%nonassoc WITH
%nonassoc below_EFFECT
%nonassoc EFFECT
%left BAR
(* %left COMMA *)
%right ARROW
(* %nonassoc IFZERO *)
%nonassoc ELSE
%left ADDOP
%left MULOP STAR
%nonassoc prec_constant_constructor
(* First tokens of atomic_term *)
%nonassoc LPAREN UIDENT IDENT INTLITERAL

%start<RawLambda.program> entry

%{

open RawLambda

%}

%%

(* -------------------------------------------------------------------------- *)

(* A toplevel phrase is just a term. *)

entry:
  p = program EOF { p }

program:
| t = any_term p = program_tail { { value = DTerm t ; place = t.place } :: p }
| p = program_tail { p }

program_tail:
| { [] }
| SEMISEMI p = program { p }
| d = decl p = program_tail { d :: p }

(* -------------------------------------------------------------------------- *)

(* The syntax of terms is stratified as follows:

   atomic_term             -- unambiguously delimited terms
   application_term        -- n-ary applications of atomic terms
   any_term                -- everything

*)

%inline decl:
| d = placed(decl_) { d }

decl_:
| LET mode = recursive x = IDENT EQ t = any_term
    { DLet (mode, x, t) }
| TYPE x = IDENT EQ l = left_flexible_list(BAR, placed(type_decl_case_))
    { DNewType (x, l) }
| TYPE x = IDENT EQ t = ty
    { DTypeSynonym (x, t) }
(*
| EFFECT x = IDENT EQ l = left_flexible_list(BAR, placed(effect_decl_case_))
    { DEffect (x, l) }
*)
| EFFECT x = IDENT EQ e = placed(effect_decl_case_)
    { DEffect (x, e) }


effect_decl_case_:
| c = UIDENT COLON t = ty
    {
      match t.value with
      | TArrow (t1, t2) -> c, Some t1, t2
      | _ -> c, None, t
    }

type_decl_case_:
| c = UIDENT { (c, []) }
| c = UIDENT OF l = separated_list(STAR, simple_type) { (c, l) }

%inline simple_type:
| t = placed(simple_type_) { t }

%inline ty:
| t = placed(ty_) { t }

ty_:
| t = simple_type_ { t }
| t = simple_type STAR l = separated_nonempty_list(STAR, simple_type)
  { TTuple (t :: l) }
| t1 = ty ARROW t2 = ty { TArrow (t1, t2) }

simple_type_:
| LPAREN t = ty_ RPAREN { t }
| x = IDENT { TVar x }

atomic_term_:
| LPAREN t = any_term_ RPAREN
    { t }
| x = IDENT
    { Var x }
| i = INTLITERAL
    { Lit i }
| x = UIDENT %prec prec_constant_constructor
    { Constructor (x, None) }

%inline atomic_term:
| t = placed(atomic_term_) { t }

application_term_:
| t = atomic_term_
    { t }
| t1 = application_term t2 = atomic_term
    { App (t1, t2) }
| PRINT t2 = atomic_term
    { Print t2 }
| CALLCC t2 = atomic_term
    { CallCc t2 }
| x = UIDENT t2 = application_term
    { Constructor (x, Some t2) }

%inline application_term:
| t = placed(application_term_) { t }

%inline binop:
| op = MULOP { op }
| STAR { OpMul }
| op = ADDOP { op }

any_term_:
| t = application_term_ { t }
| t1 = any_term op = binop t2 = any_term { BinOp (t1, op, t2) }
| FUN x = IDENT ARROW t = any_term
    { Lam (x, t) }
| LET mode = recursive x = IDENT EQ t1 = any_term IN t2 = any_term
    { Let (mode, x, t1, t2) }
| IFZERO t1 = any_term THEN t2 = any_term ELSE t3 = any_term
    { IfZero (t1, t2, t3) }
| MATCH t1 = any_term WITH cases = match_cases
    { Match (t1, cases) }
| t = application_term COMMA l = separated_nonempty_list(COMMA, application_term)
    { Tuple (t :: l) }

%inline match_cases:
| l = match_cases_ { List.rev l }

match_cases_:
| (* empty *) %prec below_EFFECT
    { [] }
| x = match_case
    { [x] }
| xs = match_cases_ BAR x = match_case
    { x :: xs }

%inline any_term:
| t = placed(any_term_) { t }

match_case:
| p = pattern ARROW t = any_term
    { (Pattern p, t) }
| EFFECT c = UIDENT p = pattern k = IDENT ARROW t = any_term
    { (Effect (c, Some p, k), t) }
| EFFECT c = UIDENT k = IDENT ARROW t = any_term
    { (Effect (c, None, k), t) }

%inline pattern:
| p = placed(pattern_) { p }

pattern_:
| p1 = pattern BAR p2 = pattern { POr (p1, p2) }
| p = simple_pattern COMMA l = separated_nonempty_list(COMMA, simple_pattern)
    { PTuple (p :: l) }
| p = simple_pattern_ { p }

%inline simple_pattern:
| p = placed(simple_pattern_) { p }

simple_pattern_:
| LPAREN p = pattern_ RPAREN { p }
| x = IDENT { PVar x }
| x = UIDENT p = ioption(simple_pattern) { PConstructor (x, p) }

(* -------------------------------------------------------------------------- *)

(* A [let] construct carries an optional [rec] annotation. *)

recursive:
| REC { Recursive }
|     { NonRecursive }

(* -------------------------------------------------------------------------- *)

(* A term is annotated with its start and end positions, for use in error
   messages. *)

%inline placed(X):
  x = X
    { { place = ($startpos, $endpos); value = x } }

(* -------------------------------------------------------------------------- *)

(* In a right-flexible list, the last delimiter is optional, i.e., [delim] can
   be viewed as a terminator or a separator, as desired. *)

(* There are several ways of expressing this. One could say it is either a
   separated list or a terminated list; this works if one uses right recursive
   lists. Or, one could say that it is a separated list followed with an
   optional delimiter; this works if one uses a left-recursive list. The
   following formulation is direct and seems most natural. It should lead to
   the smallest possible automaton. *)

right_flexible_list(delim, X):
| (* nothing *)
    { [] }
| x = X
    { [x] }
| x = X delim xs = right_flexible_list(delim, X)
    { x :: xs }

(* In a left-flexible list, the first delimiter is optional, i.e., [delim] can
   be viewed as an opening or as a separator, as desired. *)

(* Again, there are several ways of expressing this, and again, I suppose the
   following formulation is simplest. It is the mirror image of the above
   definition, so it is naturally left-recursive, this time. *)

reverse_left_flexible_list(delim, X):
| (* nothing *)
    { [] }
| x = X
    { [x] }
| xs = reverse_left_flexible_list(delim, X) delim x = X
    { x :: xs }

%inline left_flexible_list(delim, X):
  xs = reverse_left_flexible_list(delim, X)
    { List.rev xs }
