#include <stdint.h>
#include <assert.h>

/* A forward declaration of [block] -- see below. */

struct block;

static_assert(sizeof(struct block*) == sizeof(uint64_t), "Code relies on 64-bit architecture");
static_assert(sizeof(uint64_t) == 8, "Code relies on 64-bit architecture");

/* -------------------------------------------------------------------------- */

/* The type [univ] is the universal type of the values that we manipulate.
   A value is either an integer or a pointer to a heap-allocated memory
   block. A C union is used to represent this disjunction. There is no tag
   to distinguish between the two alternatives! The source program had
   better be well-typed. */

typedef union {

  /* Either this is an integer... */
  int64_t       literal;

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

static_assert (sizeof(struct block) == sizeof(univ), "");

/* -------------------------------------------------------------------------- */

/* Basic operations on memory blocks. */

/* The macro [ALLOC(n, tag)] allocates a block of [n] fields, with tag [tag],
	 and is used in a context where an expression of type [univ] is expected. */

#define MAKE_TAG(n, tag) \
	((((uint64_t) (n)) << 23) | ((tag) << 3) | 2)

extern inline struct block* gc_alloc_minor(size_t n);
extern inline univ make_block(size_t n, uint32_t tag) {
	assert (n > 0 && tag < (1 << 20));
	struct block* data = gc_alloc_minor(n + 1);
	data->tag = MAKE_TAG(n, tag);
	return (univ) { .pointer = data };
}

#define ALLOC(n, tag)	\
  (make_block((n), (tag)))

#define MAKE_TAG0(tag) \
	(((tag) << 3) | 2)

/* In the following macros, [u] has type [univ], so [u.pointer] has type
   [struct block] and is (or should be) the address of a memory block.
   [i] is a field number; the numbering of fields is 0-based. */

#define GET_TAG(u) \
  (((u).pointer->tag >> 3) & 0xfffff)

#define GET_SIZE(u) \
  ((u).pointer->tag >> 23)

#define GET_FIELD(u,i) \
  (u.pointer->data[i])

#define SET_FIELD(u,i,v) \
  (u.pointer->data[i]=v)

#define IS_INT(u) \
	((u).literal & 1)

#define IS_TAG(u) \
	(((u).literal & 3) == 2)

#define IS_POINTER(u) \
	(((u).literal & 3) == 0)

#define IS_MARKED(u) \
	((u).literal & 4)

/* -------------------------------------------------------------------------- */

/* Basic operations on integers. */

/* The macro [FROM_INT(i)] converts the integer [i] to the type [univ]. */

#define FROM_INT(i) \
  (univ) { .literal = (i) }

/* The macro [TO_INT(u)] converts [u] to the type [int]. */

#define TO_INT(u) \
  (u).literal

#define FROM_POINTER(p) \
	(univ) { .pointer = (struct block*)(p) }

/* -------------------------------------------------------------------------- */

/* GC */

#ifdef GC_DEBUG
  #define gc_debug printf
#else
  #define gc_debug(...) do {} while(0)
#endif

struct block* minor_heap_begin;
struct block* minor_heap_end;
struct block* minor_heap_allocptr;
size_t minor_heap_size = 1024;
struct block* major_heap_begin;
struct block* major_heap_end;
struct block* major_heap_allocptr;
size_t major_heap_size = 4096;

univ gc_roots[256];
size_t gc_num_roots = 0;

void gc_init() {
	minor_heap_begin = malloc(minor_heap_size * sizeof(univ));
	minor_heap_end = minor_heap_begin + minor_heap_size;
	minor_heap_allocptr = minor_heap_begin;

	major_heap_begin = malloc(major_heap_size * sizeof(univ));
	major_heap_end = major_heap_begin + major_heap_size;
	major_heap_allocptr = major_heap_begin;
}

/* Returns non-zero in case of overflow */
extern inline int gc_check_size(size_t n) {
	return (minor_heap_allocptr + n > minor_heap_end);
}

/* Unchecked allocation */
extern inline struct block* gc_alloc_minor(size_t n) {
	struct block* result = minor_heap_allocptr;
	minor_heap_allocptr += n;
	return result;
}

extern inline int gc_check_major_size(size_t n) {
	return (major_heap_allocptr + n > major_heap_end);
}

/* Unchecked allocation */
extern inline struct block* gc_alloc_major(size_t n) {
	struct block* result = major_heap_allocptr;
	major_heap_allocptr += n;
	return result;
}

extern inline void gc_set_num_roots(size_t n) {
	gc_num_roots = n;
}

extern inline void gc_set_root(size_t i, univ root) {
	gc_roots[i] = root;
}

extern inline univ gc_get_root(size_t i) {
	return gc_roots[i];
}

void gc_dump_value(univ x) {
	if (IS_INT(x)) {
		printf("(%lld)", TO_INT(x) >> 1);
		return;
	}
	printf("(%d [", GET_TAG(x));
	for (size_t i = 0; i < GET_SIZE(x); i++) {
		gc_dump_value(GET_FIELD(x, i));
	}
	printf("])");
}

univ gc_small_collect(univ x_) {
	univ x = x_;
	if (IS_INT(x))
		return x;

	univ rptr[2] = {FROM_INT(2), x};
	univ* ptr = &rptr[1];
	univ result;
	gc_debug("Init tag is %llx.\n", x.pointer->tag);
	univ* copyptr = &result;
	do {
		gc_debug("Loop at ptr = %p.\n", (void*)ptr);
		if (IS_TAG(x)) {
			if (ptr == rptr) {
				gc_debug("Result tag is %llx.\n", result.pointer->tag);
				return result;
			}
			assert (IS_MARKED(x));
			size_t bsize = GET_SIZE(FROM_INT(x.literal & ~7));
			gc_debug("End visit of block at %p and size %lld.\n", (void*)ptr, bsize);
			ptr = (univ*)((ptr + bsize)->pointer);
			gc_debug("ptr is now %p.\n", (void*)ptr);
			x = *ptr;
			continue;
		}
		univ set_val;
		if (IS_INT(x) || !(minor_heap_begin <= x.pointer && x.pointer < minor_heap_end)) {
			set_val = x;
		do_copy:
			gc_debug("Atomic copy of block at %p.\n", (void*)ptr);
			if (IS_TAG(*(copyptr - 1))) {
				univ* z = (univ*)((*copyptr).pointer);
				*copyptr = set_val;
				copyptr = z;
			} else {
				*copyptr = set_val;
				copyptr--;
			}
			ptr--;
			x = *ptr;
			continue;
		}
		assert(IS_POINTER(x));

		uint64_t tag = x.pointer->tag;
		if (IS_MARKED(FROM_INT(tag))) {
			set_val = FROM_INT(tag & ~7);
			goto do_copy;
		}

		size_t bsize = GET_SIZE(x);
		gc_debug("Begin visit of block at %p and size %lld.\n", (void*)x.pointer, bsize);
		struct block* copy_addr = gc_alloc_major(bsize + 1);
		univ* ncopyptr = copyptr - 1;
		if (IS_TAG(*ncopyptr)) {
			ncopyptr = (univ*)(copyptr->pointer);
		}
		*copyptr = FROM_POINTER(copy_addr);
		copy_addr->tag = tag;
		*(((univ*)copy_addr) + 1) = FROM_POINTER(ncopyptr);
		x.pointer->tag = (uint64_t)(copy_addr) | 6;
		copyptr = ((univ*)copy_addr) + bsize;
		univ* oldptr = ptr;
		ptr = ((univ*)x.pointer) + bsize;
		x = *ptr;
		*ptr = FROM_POINTER(oldptr - 1);
	} while (1);
}

extern inline void gc_small_collection() {
	gc_debug("Small collection.\n");
	assert(!gc_check_major_size(minor_heap_size));
#ifdef GC_DEBUG
	for (size_t i = 0; i < gc_num_roots; i++) {
		gc_dump_value(gc_roots[i]);
		printf("\n");
	}
#endif
	for (size_t i = 0; i < gc_num_roots; i++) {
		gc_roots[i] = gc_small_collect(gc_roots[i]);
	}
#ifdef GC_DEBUG
	for (size_t i = 0; i < gc_num_roots; i++) {
		gc_dump_value(gc_roots[i]);
		printf("\n");
	}
#endif
	minor_heap_allocptr = minor_heap_begin;
	gc_debug("Done.\n");
}
