%token<string> IDENT
%token<string> UIDENT
%token<int> INTLITERAL
%token FUN IN LET PRINT REC CALLCC
%token IFZERO THEN ELSE
%token ARROW EQ LPAREN RPAREN BAR COMMA
%token TYPE OF
%token MATCH WITH
%token<RawLambda.binop> MULOP ADDOP
%token EOF

%nonassoc IN
%nonassoc WITH
%left BAR
(* %left COMMA *)
%right ARROW
(* %nonassoc IFZERO *)
%nonassoc ELSE
%left ADDOP
%left MULOP

%start<RawLambda.term> entry

%{

open RawLambda

%}

%%

(* -------------------------------------------------------------------------- *)

(* A toplevel phrase is just a term. *)

entry:
  t = any_term EOF
    { t }

(* -------------------------------------------------------------------------- *)

(* The syntax of terms is stratified as follows:

   atomic_term             -- unambiguously delimited terms
   application_term        -- n-ary applications of atomic terms
   any_term                -- everything

   A [match/with/end] construct is terminated with an [end] keyword, as in Coq,
   so it is an atomic term. *)

atomic_term_:
| LPAREN t = any_term RPAREN
    { t.value }
| x = IDENT
    { Var x }
| i = INTLITERAL
    { Lit i }

application_term_:
| t = atomic_term_
    { t }
| t1 = placed(application_term_) t2 = placed(atomic_term_)
    { App (t1, t2) }
| PRINT t2 = placed(atomic_term_)
    { Print t2 }
| CALLCC t2 = placed(atomic_term_)
    { CallCc t2 }

%inline binop:
| op = MULOP { op }
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
| MATCH t1 = any_term WITH cases = left_flexible_list(BAR, match_case)
    { Match (t1, cases) }

%inline any_term:
| t = placed(any_term_) { t }

match_case:
| p = pattern ARROW t = any_term { (p, t) }

%inline pattern:
| p = placed(pattern_) { p }

pattern_:
| p1 = pattern BAR p2 = pattern { POr (p1, p2) }
| p = simple_pattern COMMA l = separated_list(COMMA, simple_pattern)
    { PTuple (p :: l) }
| p = simple_pattern_ { p }

%inline simple_pattern:
| p = placed(simple_pattern_) { p }

simple_pattern_:
| LPAREN p = pattern_ RPAREN { p }
| x = IDENT { PVar x }
| x = UIDENT { PConstructor (x, None) }
| x = UIDENT p = simple_pattern { PConstructor (x, Some p) }

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
