(* The source calculus. *)
module S = Top
(* The target calculus. *)
module T = C

module IMap = Map.Make(struct type t = int let compare = compare end)
type finish_state = {
  mutable tags0 : Atom.atom IMap.t ;
}
let empty_state () = {
  tags0 = IMap.empty ;
}

(* -------------------------------------------------------------------------- *)

(* [interval i j f] constructs the list [[f i; f (i + 1); ...; f (j - 1)]]. *)

let rec interval i j (f : int -> 'a) : 'a list =
  if i < j then
    f i :: interval (i + 1) j f
  else
    []

(* -------------------------------------------------------------------------- *)

(* [index xs] constructs a list of pairs, where each element of [xs] is paired
   with its index. Indices are 0-based. *)

let index (xs : 'a list) : (int * 'a) list =
  let n = List.length xs in
  let indices = interval 0 n (fun i -> i) in
  List.combine indices xs

(* -------------------------------------------------------------------------- *)

(* The number of fields of a block, not counting its tag. *)

let block_num_fields b =
  match b with
  | S.Con (_, vs) ->
      List.length vs

let block_tag b =
  match b with
  | S.Con (tag, _) -> tag

(* -------------------------------------------------------------------------- *)

(* A simple-minded way of ensuring that every atom is printed as a
   distinct string is to concatenate the atom's hint and identity,
   with an underscore in between. This is guaranteed to rule out
   collisions. *)

let var (x : S.variable) : T.ident =
  Printf.sprintf "%s_%d" (Atom.hint x) (Atom.identity x)

let evar (x : S.variable) : T.expr =
  T.Name (var x)

(* -------------------------------------------------------------------------- *)

(* Predefined C types and functions. *)

(* A universal type: every value is translated to a C value of type [univ].
   This is a union type (i.e., an untagged sum) of integers and pointers to
   memory blocks. *)

let univ : T.type_spec =
  T.Named "univ"

(* The type of integers. *)

let int : T.type_spec =
  T.Named "int64_t"

(* The type [char] appears in the type of [main]. *)

let char : T.type_spec =
  T.Named "char"

let answer : T.type_spec =
  T.Named "int"
    (* Our functions never actually return, since they are tail recursive.
       We use [int] as their return type, since this is the return type of
       [main]. *)

let exit : T.expr =
  T.Name "exit"

let printf : T.expr =
  T.Name "printf"

(* -------------------------------------------------------------------------- *)

(* [declare x init] constructs a local variable declaration for a variable [x]
   of type [univ]. [x] is optionally initialized according to [init]. *)

let declare (x : S.variable) (init : T.init option) : T.declaration =
  univ, None, [ T.Ident (var x), init ]

(* -------------------------------------------------------------------------- *)

(* Macro invocations. *)

let macro m es : T.expr =
  (* We disguise a macro invocation as a procedure call. *)
  T.Call (T.Name m, es)

(* -------------------------------------------------------------------------- *)

(* Integer literals; conversions between [univ] and [int]. *)

let iconst i : T.expr =
  T.Constant (Constant.Int64, string_of_int i)

let to_int v : T.expr =
  macro "TO_INT" [ v ]
    (* This is an unsafe conversion, of course. *)

let from_int v : T.expr =
  macro "FROM_INT" [ v ]

(* -------------------------------------------------------------------------- *)

(* The translation of values. *)

let finish_op op v1 v2 =
  match op with
  | S.OpAdd ->
    T.Op2 (T.K.Sub, T.Op2 (T.K.Add, v1, v2), iconst 1)
  | S.OpSub ->
    T.Op2 (T.K.Add, T.Op2 (T.K.Sub, v1, v2), iconst 1)
  | S.OpMul ->
    T.Op2 (T.K.Add, T.Op2 (T.K.Mult,
                           T.Op2 (T.K.Sub, v1, iconst 1),
                           T.Op2 (T.K.BShiftR, v2, iconst 1)
                          ), iconst 1)
  | S.OpDiv ->
    T.Op2 (T.K.Add, T.Op2 (T.K.BShiftL,
                           T.Op2 (T.K.Div,
                                  T.Op2 (T.K.Sub, v1, iconst 1),
                                  T.Op2 (T.K.Sub, v2, iconst 1)),
                           iconst 1), iconst 1)

let rec finish_value (v : S.value) : T.expr =
  match v with
  | S.VVar x ->
     evar x
  | S.VLit i ->
     from_int (iconst (2 * i + 1))
  | S.VBinOp (v1, op, v2) ->
    from_int (finish_op op
                (to_int (finish_value v1))
                (to_int (finish_value v2)))

let finish_values vs =
  List.map finish_value vs

(* -------------------------------------------------------------------------- *)

let get_tag0 st tag =
  try IMap.find tag st.tags0
  with Not_found ->
    let a = Atom.fresh ("tag0_" ^ string_of_int tag ^ "_") in
    st.tags0 <- IMap.add tag a st.tags0;
    a

(* A macro for allocating a memory block. *)

let alloc st b : T.expr =
  if block_num_fields b = 0 then
    let a = get_tag0 st (block_tag b) in
    macro "FROM_POINTER" [T.Address (evar a)]
  else
    T.Call (T.Name "ALLOC", [ iconst (block_num_fields b) ; iconst (block_tag b) ])

let rec fct_max_total_alloc (t : S.term) =
  match t with
  | S.Exit | S.TailCall _ -> 0
  | S.Print (_, t) | S.LetVal (_, _, t) -> fct_max_total_alloc t
  | S.IfZero (_, t1, t2) -> max (fct_max_total_alloc t1) (fct_max_total_alloc t2)
  | S.LetBlo (_, b, t) -> fct_max_total_alloc t + block_num_fields b + 1
  | S.Swi (_, l, t) ->
    let c = match t with None -> 0 | Some t -> fct_max_total_alloc t in
    let l = List.map (fun (S.Branch (_, _, t)) -> fct_max_total_alloc t) l in
    List.fold_left max c l

(* -------------------------------------------------------------------------- *)

(* Macros for reading the tag of a memory block. *)

let read_tag (v : S.value) : T.expr =
  macro "GET_TAG" [ finish_value v ]

(* -------------------------------------------------------------------------- *)

(* Macros for reading and setting a field in a memory block. *)

let read_field (v : S.value) (i : int) : T.expr =
  (* [i] is a 0-based field index. *)
  macro "GET_FIELD" [ finish_value v; iconst i ]

let read_field (v : S.value) (i, x) (t : T.stmt list) : T.stmt list =
  (* [x] is a variable, which is declared and initialized with
     the content of the [i]th field of the block [v]. *)
  T.DeclStmt (declare x (Some (T.InitExpr (read_field v i)))) ::
  t

let read_fields (v : S.value) xs (t : T.stmt list) : T.stmt list =
  (* [xs] are variables, which are declared and initialized with
     the contents of the fields of the block [v]. *)
  List.fold_right (read_field v) (index xs) t

let set_field x i (v : S.value) : T.stmt =
  T.Expr (macro "SET_FIELD" [ evar x; iconst i; finish_value v ])

(* -------------------------------------------------------------------------- *)

(* A sequence of instructions for initializing a memory block. *)

let init_block (x : S.variable) (b : S.block) : T.stmt list =
  match b with
  | S.Con (_, []) -> []
  | S.Con (_, vs) ->
      T.Comment "Initializing a memory block:" ::
      List.mapi (set_field x) vs

(* -------------------------------------------------------------------------- *)

(* Function calls, as expressions and as statements. *)

let ecall f args : T.expr =
  T.Call (f, args)

let scall f args : T.stmt =
  T.Expr (ecall f args)

(* -------------------------------------------------------------------------- *)

(* The translation of terms. *)

let rec finish_term (st : finish_state) (t : S.term) : C.stmt =
  match t with
  | S.Exit ->
    T.Compound [
      scall exit [ iconst 0 ]
    ]
  | S.TailCall (f, vs) ->
    T.Return (Some (ecall (evar f) (finish_values vs)))
  | S.Print (v, t) ->
    T.Compound [
      scall printf [ T.Literal "%lld\\n";
                     T.Op2 (T.K.BShiftR, to_int (finish_value v), iconst 1) ];
      finish_term st t
    ]
  | S.LetVal (x, v1, t2) ->
    T.Compound [
      T.DeclStmt (declare x (Some (T.InitExpr (finish_value v1))));
      finish_term st t2
    ]
  | S.LetBlo (x, b1, t2) ->
    T.Compound (
      T.DeclStmt (declare x (Some (T.InitExpr (alloc st b1)))) ::
      init_block x b1 @
      [ finish_term st t2 ]
    )
  | S.Swi (v, bs, t) ->
    T.Switch (
      read_tag v,
      finish_branches st v bs,
      match t with None -> default | Some t -> finish_term st t
    )
  | S.IfZero (v, t1, t2) ->
    T.IfElse (T.Op2 (T.K.Sub, to_int (finish_value v), iconst 1),
              finish_term st t2, finish_term st t1)

and default : T.stmt =
  (* This default [switch] branch should never be taken. *)
  T.Compound [
    scall printf [ T.Literal "Oops! A nonexistent case has been taken (line %d).\\n" ; T.Name "__LINE__" ];
    scall exit [ iconst 42 ];
  ]

and finish_branches st v bs =
  List.map (finish_branch st v) bs

and finish_branch st v (S.Branch (tag, xs, t)) : T.expr * T.stmt =
  iconst tag,
  T.Compound (read_fields v xs [finish_term st t])

(* -------------------------------------------------------------------------- *)

(* Function declarations. *)

(* We distinguish the function [main], whose type is imposed by the C standard,
   and ordinary functions, whose parameters have type [univ]. *)

(* A parameter of an ordinary function has type [univ]. *)

let param (x : S.variable) : T.param =
  univ, T.Ident (var x)

(* A declaration of an ordinary function. *)

let declare_ordinary_function f xs : T.declaration =
  answer, None, [ T.Function (None, T.Ident (var f), List.map param xs), None ]

(* The declaration of the main function. *)

let declare_main_function : T.declaration =
  let params = [
    T.Named "int", T.Ident "argc";
    char, T.Pointer (T.Pointer (T.Ident "argv"))
  ] in
  T.Named "int", None, [ T.Function (None, T.Ident "main", params), None ]

(* -------------------------------------------------------------------------- *)

(* A function definition. *)

type decl_or_fun =
  T.declaration_or_function

let define (decl : T.declaration) (st : finish_state) (t : S.term) : decl_or_fun =
  T.Function (
    [],    (* no comments *)
    false, (* not inlined *)
    decl,
    T.Compound [finish_term st t]
  )

let define_ordinary_function (st : finish_state) (S.Fun (f, xs, t)) : decl_or_fun =
  let b = fct_max_total_alloc t in
  let chk = ecall (T.Name "gc_check_size") [iconst b] in
  let gc_msg = scall (T.Name "gc_debug") [T.Literal "Calling gc at line %d.\\n" ; T.Name "__LINE__"] in
  let set_num_roots = scall (T.Name "gc_set_num_roots") [iconst (List.length xs)] in
  let save_vars = List.mapi (fun i x -> scall (T.Name "gc_set_root") [iconst i; evar x]) xs in
  let collect = scall (T.Name "gc_small_collection") [] in
  let restore_vars = List.mapi (fun i x -> T.Expr (T.Assign (evar x, ecall (T.Name "gc_get_root") [iconst i]))) xs in
  let checkblk = T.If (chk, T.Compound (gc_msg :: set_num_roots :: save_vars @ [collect] @ restore_vars)) in
  T.Function (
    [],
    false,
    (declare_ordinary_function f xs),
    T.Compound [checkblk; finish_term st t]
  )

let define_main_function (st : finish_state) (t : S.term) : decl_or_fun =
  T.Function (
    [],
    false,
    declare_main_function,
    T.Compound [scall (T.Name "gc_init") []; finish_term st t]
  )

(* -------------------------------------------------------------------------- *)

(* Because all functions are mutually recursive, their definitions must be
   preceded with their prototypes. *)

let prototype (f : decl_or_fun) : decl_or_fun =
  match f with
  | T.Function (_, _, declaration, _) ->
      T.Decl ([], declaration)
  | T.Decl _ ->
      assert false

let prototypes (fs : decl_or_fun list) : decl_or_fun list =
  List.map prototype fs @
  fs

let declare_tags0 (st : finish_state) : decl_or_fun list =
  st.tags0
  |> IMap.bindings
  |> List.map (fun (tag, a) ->
      let init = Some (T.InitExpr (macro "MAKE_TAG0" [iconst tag])) in
      T.Decl ([], (T.Named "uint64_t", None, [T.Ident (var a), init]))
    )

(* -------------------------------------------------------------------------- *)

(* The translation of a complete program. *)

let finish_program (S.Prog (decls, main) : S.program) : T.program =
  let st = empty_state () in
  let main = define_main_function st main in
  let decls = List.map (define_ordinary_function st) decls in
  declare_tags0 st @ prototypes (main :: decls)
