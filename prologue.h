#include <stdint.h>

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
  uint64_t tag;

  /* Then, we have a sequence of fields, whose number depends on the tag.
     This idiom is known in C99 as a flexible array member. */
  univ data[];

};

/* -------------------------------------------------------------------------- */

/* Basic operations on memory blocks. */

/* The macro [ALLOC(n, tag)] allocates a block of [n] fields, with tag [tag],
	 and is used in a context where an expression of type [univ] is expected. */

inline univ make_block(size_t n, uint32_t tag) {
	struct block* data = malloc(sizeof(uint64_t) + n * sizeof(univ));
	data->tag = (((uint64_t) n) << 21) | (tag << 1) | 1;
	return (univ) { .pointer = data };
}

#define ALLOC(n, tag)	\
  (make_block((n), (tag)))

/* In the following macros, [u] has type [univ], so [u.pointer] has type
   [struct block] and is (or should be) the address of a memory block.
   [i] is a field number; the numbering of fields is 0-based. */

#define GET_TAG(u) \
  (((u).pointer->tag >> 1) & 0xfffff)

#define GET_SIZE(u) \
  ((u).pointer->tag >> 21)

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
