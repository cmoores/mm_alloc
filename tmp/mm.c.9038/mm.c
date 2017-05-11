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
    "Moores_Clayton",
    /* First member's full name */
    "Christopher Moores",
    /* First member's email address */
    "cmoores@udel.edu",
    /* Second member's full name (leave blank if none) */
    "Christopher Clayton",
    /* Second member's email address (leave blank if none) */
    "chrisbme@udel.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define CHUNKSIZE   (1<<12)
#define WSIZE       4
#define DSIZE       8

#define MAX(x, y)   ((x) > (y)? (x):(y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc)   ((size) | (alloc))

// Read and write a word at address p
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// Read the size and allocated fields from address p
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


// Global variables
static char *heap_listp = 0; 
// static char *free_listp = 0;

// Helper subroutines
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void *find_fit(size_t asize){
    void *bp;

    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp= NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL; // no fit
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){               // case 1
        return bp;
    }   
    else if(prev_alloc && !next_alloc){         // case 2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){         // case 3
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    }
    else{                                       // case 4
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    }
    return bp;

}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // Allocate an even number of words to maintain alignment
    size = (words%2) ? (words+1)*WSIZE: words * WSIZE;


    // if(size < 16){
    //     size = 16;         // since header and footer total 8 and payload cannot be zero, min size rounds to 16
    // }

    if((long)(bp=mem_sbrk(size)) == -1){
        return NULL;
    }
    // Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));               // Free block header
    PUT(FTRP(bp), PACK(size, 0));               // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       // new epilogue header

    // Coalesce if the previous block was free
    return coalesce(bp);
}




// // heap_block struct
// struct heap_block{
//   size_t payload;             // size of the payload
//   struct heap_block* next_free;  // points to the next free block in the heap
//   struct heap_block* prev_free;  // points to the previous free block in the heap
// };

// // initialize the heap struct data type 
// typedef struct heap_block heap_block;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // Create the initial empty heap
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0);                             // Alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // Epilogue header
    heap_listp += (2*WSIZE);

    // Extend the empty heap with a free block of CHUNKSIZE bytes
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
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
    size_t asize;
    size_t extendsize;
    char *bp;

    // ignore spurious requests
    if(size == 0){
        return NULL;
    }

    // adjust block size to include overhead and alignment reqs
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1))/DSIZE);
    }

    // Search the free list for a fit
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    // No fit found. Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;


 //    int newsize = ALIGN(size + SIZE_T_SIZE);
 //    void *p = mem_sbrk(newsize);
 //    if (p == (void *)-1)
	// return NULL;
 //    else {
 //        *(size_t *)p = size;
 //        return (void *)((char *)p + SIZE_T_SIZE);
 //    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    if(ptr == NULL){
        return;
    }

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
    size_t copySize = MAX(ALIGN(size), 24);
    size_t oldsize;


    // if ptr is NULL, the call is equivalent to mm malloc(size);
    if(ptr == NULL){
        return malloc(size);
    }
    // if size is equal to zero, the call is equivalent to mm free(ptr);
    if(size == 0){
        free(ptr);
    }

    oldsize = GET_SIZE(HDRP(ptr)); // ptr is not null and 

    //      if the newsize = oldsize, no changes and return old ptr  
    if(copySize == oldsize){
        return ptr;
    }


    //     if ptr is not NULL, it must have been returned by an earlier call to mm malloc or mm realloc.
    // The call to mm realloc changes the size of the memory block pointed to by ptr (the old
    // block) to size bytes and returns the address of the new block. Notice that the address of the
    // new block might be the same as the old block, or it might be different, depending on your implementation,
    // the amount of internal fragmentation in the old block, and the size of the realloc
    // request.
    if(ptr != NULL && (copySize < oldsize)){ //redundant ptr != NULL ???
        size = copySize;


    //      The contents of the new block are the same as those of the old ptr block, up to the minimum of
    // the old and new sizes. Everything else is uninitialized. For example, if the old block is 8 bytes
    // and the new block is 12 bytes, then the first 8 bytes of the new block are identical to the first 8
    // 2
    // bytes of the old block and the last 4 bytes are uninitialized. Similarly, if the old block is 8 bytes
    // and the new block is 4 bytes, then the contents of the new block are identical to the first 4 bytes
    // of the old block.

        // if there is already room to add block, return the addr of the pointer
        if (oldsize - size <= 24){
            return ptr;
        }
        else{

            size_t newsize = oldsize - size;
            PUT(HDRP(ptr), PACK(size, 1));      // set occupy bit to true
            PUT(FTRP(ptr), PACK(size, 1));      // set occupy bit to true
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(newsize, 1));
            free(NEXT_BLKP(ptr));               // free the requested space

            return ptr;
        }
    }

    // allocate my new space that I requested, and return my new pointer
    newptr = malloc(size);

    if(newptr == NULL){
        return 0;
    }
    // 
    else if(size < oldsize){
        oldsize = size;
    }

    //return all of the data in old blocks (all of it, only it)
    memcpy(newptr, ptr, oldsize);
    // using the new address, lets free the old one
    free(ptr);

    // now return my new address
    return newptr;

}

int mm_check(void){
    return 0;
}













