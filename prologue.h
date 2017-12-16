/* A forward declaration of [block] -- see below. */

struct block;

/* -------------------------------------------------------------------------- */

/* The type [univ] is the universal type of the values that we manipulate.
   A value is either an integer or a pointer to a heap-allocated memory
   block. A C union is used to represent this disjunction. There is no tag
   to distinguish between the two alternatives! The source program had
   better be well-typed. */

typedef union {

  /* Either this is an integer... */
  int           literal;

  /* ... or this is a pointer to a block. */
  struct block* pointer;

} univ;

/* -------------------------------------------------------------------------- */

/* The struct [block] describes the uniform layout of a heap-allocated
   memory block. A block begins with an integer tag and continues with a
   sequence of fields of type [univ]. */

struct block {

  /* Every memory block begins with an integer tag. */
  int tag;

  /* Then, we have a sequence of fields, whose number depends on the tag.
     This idiom is known in C99 as a flexible array member. */
  univ data[];

};

/* -------------------------------------------------------------------------- */

/* Basic operations on memory blocks. */

/* The macro [ALLOC(n)] allocates a block of [n] fields, and is used in a
   context where an expression of type [univ] is expected. We use a C
   "compound literal" containing a "designated initializer" to indicate
   that we wish to choose the "pointer" side of the union. We implicitly
   assume that the compiler inserts no padding between the "tag" and "data"
   parts of a memory block, so [(n + 1) * sizeof(univ)] is enough space to
   hold a block of [n] fields. */

#define ALLOC(n) \
  (univ) { .pointer = malloc((n + 1) * sizeof(univ)) }

/* In the following macros, [u] has type [univ], so [u.pointer] has type
   [struct block] and is (or should be) the address of a memory block.
   [i] is a field number; the numbering of fields is 0-based. */

#define GET_TAG(u) \
  (u.pointer->tag)

#define SET_TAG(u,t) \
  (u.pointer->tag = t)

#define GET_FIELD(u,i) \
  (u.pointer->data[i])

#define SET_FIELD(u,i,v) \
  (u.pointer->data[i]=v)

/* -------------------------------------------------------------------------- */

/* Basic operations on integers. */

/* The macro [FROM_INT(i)] converts the integer [i] to the type [univ]. */

#define FROM_INT(i) \
  (univ) { .literal = i }

/* The macro [TO_INT(u)] converts [u] to the type [int]. */

#define TO_INT(u) \
  u.literal
