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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Word and header/footer size (bytes) */
#define WSIZE 4
/* Double word size (bytes) */
#define DSIZE 8
/* Heap extend amount (4KB) */
#define CHUNKSIZE (1 << 12)
/* Return bigger one */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/* Put allocated or not info in last bit */
#define PACK(size, alloc) ((size) | (alloc))
/* Read or write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* Make lower 3bits to 0 and get size */
#define GET_SIZE(p) (GET(p) & ~0x7)
/* Make all bits to 0 except for last bit and get whether allocated or not */
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, get header's/footer's address */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, get address of blocks before and after */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
static char *heap_listp;
static char *start_nextfit = 0;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        /* if mem_sbrk fails */
        return -1;
    }

    /* Alignment padding */
    PUT(heap_listp, 0);
    /* Prologue header */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    /* Prologue footer */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    /* Epilogue header */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    /* Skip prologue header which is start of free list */
    heap_listp += (2 * WSIZE);
    /* Set start of next-fit as start of free list */
    start_nextfit = heap_listp;

    /* Add space for data to be stored */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
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
    /* size of block */
    size_t asize;
    /* size of heap extension if needed */
    size_t extendsize;
    char *bp;

    /* ignore unnecessary request */
    if (size == 0)
        return NULL;

    /* header + footer is DSIZE, if size is smaller then DSIZE give twice the size */
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        /* if bigger then DSIZE, resize to appropriate size*/
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }
    /* if appropriate block found */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    /* if appropriate block doesn't exit in heap, extend */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    /* change status to availiable */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    /* connect with nearby availiable blocks */
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL)
    {
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if (newp == NULL)
    {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize)
    {
        oldsize = size;
    }
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    /* allocate even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    /* create free block header and footer */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    /* update epilogue header's position */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* if prev block was free block connect */
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    /* whether prev/next block was free */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    /* size of current block */
    size_t size = GET_SIZE(HDRP(bp));

    /* if both prev next are allocated return */
    if (prev_alloc && next_alloc)
    {
        start_nextfit = bp;
        return bp;
    }
    /* if next block is free */
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* if prev block is free */
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* if both prev and next are free */
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    start_nextfit = bp;
    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp;
    /* find appropriate block starting from last allocated position */
    for (bp = start_nextfit; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    /* if not found at backside look for block at frontside */
    for (bp = heap_listp; bp != start_nextfit; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
