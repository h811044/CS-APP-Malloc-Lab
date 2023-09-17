/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define CHUNKSIZE (1 << 12)     /* initial heap size (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a size_t word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a size_t word at address p */
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - SIZE_T_SIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - SIZE_T_SIZE * 2)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - SIZE_T_SIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - SIZE_T_SIZE * 2))

static char *heap_listp;

static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* create the initial empty heap */
    if ((int)(heap_listp = mem_sbrk(SIZE_T_SIZE * 3)) == -1) {
        return -1;
    }
    PUT(heap_listp, PACK(SIZE_T_SIZE, 1));              /* prologue header */
    PUT(heap_listp+SIZE_T_SIZE, PACK(SIZE_T_SIZE, 1));  /* prologue footer */
    PUT(heap_listp+SIZE_T_SIZE*2, PACK(0, 1));          /* epilogue header */
    heap_listp += SIZE_T_SIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL) {
        return -1;
    }

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t extendsize;  /* amount to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests */
    if (size <= 0) {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs */
    size = ALIGN(size + SIZE_T_SIZE * 2);

    /* Search the free list for a fit */
    if ((bp = find_fit(size)) != NULL) {
        place(bp, size);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(size, CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL) {
        return NULL;
    }
    place(bp, size);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t oldSize;

    /* Ignore spurious requests */
    if (size <= 0) {
        return NULL;
    }

    oldSize = GET_SIZE(HDRP(ptr)) - SIZE_T_SIZE * 2;
    if (size <= oldSize) {
        /* Adjust block size to include overhead and alignment reqs */
        size = ALIGN(size + SIZE_T_SIZE * 2);
        place(oldptr, size);
        newptr = oldptr;
    } else {
        newptr = mm_malloc(size);
        if (newptr == NULL) {
            return NULL;
        }
        memcpy(newptr, oldptr, oldSize);
        mm_free(oldptr);
    }

    return newptr;
}

static void *extend_heap(size_t size)
{
    void *bp;

    /* To maintain alignment */
    size = ALIGN(size);
    if ((int)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return bp;
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        return (PREV_BLKP(bp));
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        size += GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        return (PREV_BLKP(bp));
    }
}

static void *find_fit(size_t size)
{
    void *bp;

    /* first fit search */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;    /* no fit */
}

static void place(void *bp, size_t size)
{
    size_t fsize = GET_SIZE(HDRP(bp));

    if ((fsize - size) >= ALIGN(1 + SIZE_T_SIZE * 2)) {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(fsize - size, 0));
        PUT(FTRP(bp), PACK(fsize - size, 0));
    } else {
        PUT(HDRP(bp), PACK(fsize, 1));
        PUT(FTRP(bp), PACK(fsize, 1));
    }
}
