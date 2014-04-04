/*
 * mm.c
 * hbovik - Harry Bovik
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a full description of your solution.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

//Set word and double wordSize
#define WORDSIZE 4
#define DOUBLEWORDSIZE 8
#define ALLOCATED 1
#define FREE 0
#define CHUNKSIZE 1<<16

//remove after complete implementation
#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


static uint32_t* heap_listp;
static void *coalesce (void *blockPtr);
static void *extend_heap(uint32_t words);
static void block_place(uint32_t *blockPtr, uint32_t checkSize);
/*
 *  Helper functions
 *  ----------------
 */

//block[0] == header
//block[block_size(block)+1] == footer

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const *p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

// Return the size of the given block in multiples of the word size
static inline unsigned int block_size(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (block[0] & 0x3FFFFFFF);
}

// Return true if the block is free, false otherwise
static inline int block_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(block[0] & 0x40000000);
}

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
static inline void block_mark(uint32_t* block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int next = block_size(block) + 1;
    block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
    block[next] = block[0];
}

// Return a pointer to the memory malloc should return
static inline uint32_t* block_mem(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 1));

    return block + 1;
}

// Return the header to the previous block
static inline uint32_t* block_prev(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block - block_size(block - 1) - 1;
}

// Return the header to the next block
static inline uint32_t* block_next(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block + block_size(block) + 1;
}



//Read value at address
static inline uint32_t block_getValAtPtr(uint32_t* const ptr ){
    REQUIRES(ptr != NULL);
    
    uint32_t value;
    
    value = (*ptr);
    
    return value;
    
}

//Write value to address
static inline void block_setValAtPtr(uint32_t* const ptr, int value ){
    
    REQUIRES(ptr != NULL);
    
    *ptr = value;
    
}


//Generate header and footer content
static inline uint32_t block_pack(int size,int allocated){
    
    REQUIRES(allocated == 1 || allocated == 0);
    
    int headfootValue = (allocated<<30) | (size);
    return headfootValue;
    
}


/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    if((heap_listp = mem_sbrk(4 * WORDSIZE)) == (void *) -1){
        return -1;
    }
    block_setValAtPtr(heap_listp, 0);
    block_setValAtPtr(heap_listp + 1, block_pack(DOUBLEWORDSIZE/WORDSIZE, ALLOCATED));
    block_setValAtPtr(heap_listp + 2 , block_pack(DOUBLEWORDSIZE/WORDSIZE, ALLOCATED));
    block_setValAtPtr(heap_listp + 3, block_pack(0, ALLOCATED));
    heap_listp++;
    heap_listp++;
    
    if((uint32_t *)extend_heap(CHUNKSIZE/WORDSIZE) == NULL){
        return -1;
    }
    return 0;
}


static void *extend_heap(uint32_t words){
    uint32_t *blockPtr;
    uint32_t *nextBlock;
    uint32_t *result;
    
    //For allocation of even number of words in a heap
    uint32_t size = (words %2) ? (words+1) * WORDSIZE : words * WORDSIZE;
    
    if((uint32_t)(blockPtr = mem_sbrk(size)) == -1){
        return NULL;
    }
    // Initialize free block header footer and epilogue
    block_setValAtPtr(&blockPtr[0], block_pack(size/WORDSIZE, FREE)); //free block header
    block_setValAtPtr(&blockPtr[block_size(blockPtr) - 1], block_pack(size/WORDSIZE, FREE)); //free
                                                                //block footer

    nextBlock = block_next(blockPtr);
    
    //Set epilogue block with no size as Allocated
    block_setValAtPtr(&nextBlock[0], block_pack(0,ALLOCATED));
    
    //if previous block was free coalesce
    result = (uint32_t *)coalesce(blockPtr);
    return result;
}



static void *coalesce (void *blockPtr){
    
    REQUIRES(blockPtr!=NULL);
    
    uint32_t isPreviousFree = block_free(block_prev((uint32_t *)blockPtr));
    uint32_t isNextFree = block_free(block_next((uint32_t *)blockPtr));
    uint32_t size = block_size(blockPtr);
    
    if(!isPreviousFree && !isNextFree){
        return blockPtr;
    }
    else if(!isPreviousFree && isNextFree) {
        
        uint32_t *nextPtr  = block_next(blockPtr);
        size = size + block_size(nextPtr);
        block_setValAtPtr(&blockPtr[0], block_pack(size, FREE));
        block_setValAtPtr(&blockPtr[size-1], block_pack(size, FREE));
        
        
    }
    
    else if(isPreviousFree && !isNextFree){
    
        uint32_t *prevPtr  =   block_prev(blockPtr);
        size = size + block_size(prevPtr);
        block_setValAtPtr(&prevPtr[0], block_pack(size, FREE));
        block_setValAtPtr(&prevPtr[size-1], block_pack(size, FREE));
        

    }
    
    else if(isPreviousFree && isNextFree){
        
       uint32_t *prevPtr  =   block_prev(blockPtr);
       uint32_t *nextPtr  = block_next(blockPtr);
       uint32_t sizePrev = block_size(prevPtr);
       uint32_t sizeNext = block_size(nextPtr);
        size += sizeNext+sizePrev;
        block_setValAtPtr(&prevPtr[0], block_pack(size, FREE));
        block_setValAtPtr(&nextPtr[size-1], FREE);
    
    
    }
    
    return blockPtr;
}

/*
 * Find fit
 */

void *find_fit(uint32_t size){
    uint32_t wSize = size/WORDSIZE;
    uint32_t *traverser = ++heap_listp;
    uint32_t freeSize = block_size(traverser);
    uint32_t isFree = block_free(traverser);
    while((freeSize!=wSize) || traverser != NULL){
        if(isFree && wSize <= freeSize - 2){
            
            return traverser;
        
        }
        traverser = block_next(traverser);
        isFree = block_free(traverser);
    }
    
    return NULL;
}


/*
 * malloc
 */
void *malloc (size_t size) {
    checkheap(1);  // Let's make sure the heap is ok!
    uint32_t usize = (uint32_t)size;
    uint32_t checkSize;
    uint32_t extendHeapSize;
    uint32_t *blockPtr;
    
    if(size == 0){
        return NULL;
    }
    
    else if(size<=DOUBLEWORDSIZE){
        checkSize = DOUBLEWORDSIZE * 2;
        
    }
    else{
        
        checkSize = DOUBLEWORDSIZE *((usize + (DOUBLEWORDSIZE) +(DOUBLEWORDSIZE-1))/DOUBLEWORDSIZE);
        
    }
    
    //Search the free list for a fit
    if ((blockPtr = find_fit(checkSize))!=NULL) {
        
        block_place(blockPtr,checkSize);
        return blockPtr;
    }
    
    //If no fit found
    extendHeapSize = checkSize > CHUNKSIZE? checkSize : CHUNKSIZE;
    if((blockPtr = extend_heap(extendHeapSize/WORDSIZE)) == NULL){
        
        return NULL;
        
    }
    
    block_place(blockPtr,checkSize);
    return blockPtr;
    
}

void block_place(uint32_t *blockPtr, uint32_t chkSize){
    
    uint32_t freeSize = block_size(blockPtr);
    uint32_t checkSize = chkSize/WORDSIZE;
    block_setValAtPtr(&blockPtr[0], block_pack(checkSize+2, ALLOCATED));
    block_setValAtPtr(&blockPtr[checkSize +1], block_pack(checkSize+2, ALLOCATED));
    
    if((freeSize - checkSize-2)==1){
        
        block_setValAtPtr(&blockPtr[checkSize +2], block_pack(0, ALLOCATED));
        
    }
    else if((freeSize - checkSize - 2) == 2){
        block_setValAtPtr(&blockPtr[checkSize +2], block_pack(0, ALLOCATED));
        block_setValAtPtr(&blockPtr[checkSize +3], block_pack(0, ALLOCATED));
        
    }
    
    else if (freeSize - checkSize - 2 > 2){
        
        block_setValAtPtr(&blockPtr[checkSize +2], block_pack(freeSize-checkSize - 2, FREE));
        
    }
    
}


/*
 * free
 */
void free (void *ptr) {
    
    REQUIRES(ptr!=NULL);
    uint32_t size = block_size(ptr);
    block_setValAtPtr(&ptr[0], block_pack(size, FREE));
    block_setValAtPtr(&ptr[size - 1], block_pack(size, FREE));
    coalesce(ptr);

}



/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;
    
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }
    
    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }
    
    newptr = malloc(size);
    
    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }
    
    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);
    
    /* Free the old block. */
    free(oldptr);
    
    return newptr;
}



/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;
    
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    
    return newptr;
}


// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    verbose = verbose;
    return 0;
}
