/*
* mm-implicit.c -  Simple allocator based on implicit free lists,
*                  first fit placement, and boundary tag coalescing.
*
* Each block has header and footer of the form:
*
*      31                     3  2  1  0
*      -----------------------------------
*     | s  s  s  s  ... s  s  s  0  0  a/f
*      -----------------------------------
*
* where s are the meaningful size bits and a/f is set
* iff the block is allocated. The list has the following form:
*
* begin                                                          end
* heap                                                           heap
*  -----------------------------------------------------------------
* |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
*  -----------------------------------------------------------------
*          |       prologue      |                       | epilogue |
*          |         block       |                       | block    |
*
* The allocated prologue and epilogue blocks are overhead that
* eliminate edge conditions during coalescing.
*/
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"
//#define VERBOSE 1
//#define checkheap  
//#define printre
//#define printalloc
/*
* If NEXT_FIT defined use next fit search, else use first fit search
*/
//#define NEXT_FIT

/* Team structure */
team_t team = {

	"implicit next fit",

	"1160610505"," Gan Yao",
	"",""
};
/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define POINTER_OVERHEAD   24   /* overhead of pointer: parent, left and right */
#define TREE_ROOT 8 /* tree root pointer at heap_listp */
typedef unsigned long long address_t;
typedef unsigned long long block_t;
//typedef unsigned int size_t;
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define GET_ADDRESS(p) ((block_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  
#define PUT_ADDRESS(p,val) (*(block_t *)(p) = (block_t)(val)) 
//#define PUT_ADDRESS1(p,val) ((block_t)(p) = (block_t)(val)) 
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* you can only use GET_SIZE, since block in tree must be freed */
#define GET_SIZE_ALLOC(p) (GET_SIZE(p)|GET_ALLOC(p))
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((block_t*) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))))
#define PREV_BLKP(bp) ((block_t*) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))))
#define IS_RED(p) ((GET(HDRP(p))>>1)&0x1)
#define RED 1
#define BLACK 0
#define PARENT_BLKP(bp)   ((block_t *)((char* )(bp)))
#define LEFT_BLKP(bp)  ((char* )(bp)+DSIZE)
#define RIGHT_BLKP(bp) ((block_t*)((char* )(bp)+2*DSIZE))
#define PARENT_BLK(bp)   (*(block_t*)((char *)(bp)))
#define LEFT_BLK(bp)  (*(block_t*)((((char*)(bp))+DSIZE)))
#define RIGHT_BLK(bp) (*(block_t*)((((char*)(bp))+2*DSIZE)))
/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */
static int free_call_count = 0;
static int malloc_call_count = 0;
static char *heap_end;
/* function prototypes for internal helper routines */
void mm_checkheap(int verbose);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void place_out_tree(void *bp, size_t asize);
static void *find_fit_in_tree(size_t asize);
static void *find_fit_out_tree(size_t asize);
/* do tree insert and delete in coalesce and find_fit_in_tree */

static void tree_insert(block_t *bp);
static void tree_delete(block_t *bp);
static void right_rotate(block_t *bp);
static void transplant(block_t* u, block_t* v);
static void left_rotate(block_t *bp);
static void delete_fixup(block_t *bp, block_t *par);
static void insert_fixup(block_t *bp);
static block_t* minimum(block_t* bp);

static void *coalesce(void *bp);  /* called in free, find_fit_in_tree and extend_heap */
static void printblock(void *bp);
static void checkblock(void *bp);
int mm_init(void)
{
	//printf("\nmm_init in\n");
	char * bp = NULL;
	/* create the initial empty heap */
	if ((heap_listp = mem_sbrk(4*WSIZE+3 * DSIZE)) == NULL)
		return -1;
	/* initialize tree root */
	/* put tree root size */
	PUT(heap_listp, 0);
	//PUT(heap_listp + WSIZE, 0);
	PUT(heap_listp + WSIZE, PACK(POINTER_OVERHEAD + OVERHEAD, 1));  /* prologue header */
	PUT_ADDRESS(heap_listp + DSIZE, NULL);     /* put root tree address*/
		
	PUT_ADDRESS(heap_listp + 2 * DSIZE, NULL); /* left is null */
	PUT_ADDRESS(heap_listp + 3 * DSIZE, NULL); /* right is null */
	
	PUT(heap_listp + 4 * DSIZE, PACK(POINTER_OVERHEAD + OVERHEAD, 1));  /* prologue footer */
	PUT(heap_listp + WSIZE + 4 * DSIZE, PACK(0, 1));   /* epilogue header */
		
	heap_listp += DSIZE;

	

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if ((bp = extend_heap(CHUNKSIZE / WSIZE)) == NULL)
		return -1;

#ifdef checkheap
	mm_checkheap(VERBOSE);
#endif // checkheap
	//printf("\nmm_init out\n");
	return 0;
}
/* $end mminit */


/*
* mm_malloc - Allocate a block with at least size bytes of payload
*/
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
	//printf("\nmalloc in: malloc count: %d\n",malloc_call_count++);
#ifdef checkheap
		mm_checkheap(VERBOSE);
#endif // checkheap
	size_t asize;      /* adjusted block size */
	size_t extendsize; /* amount to extend heap if no fit */
	char *bp;

	/* Ignore spurious requests */
	if (size <= 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE + POINTER_OVERHEAD)
		asize = DSIZE + OVERHEAD + POINTER_OVERHEAD;
	else
		asize = DSIZE * ((size +POINTER_OVERHEAD+(OVERHEAD)+(DSIZE - 1)) / DSIZE);

	/* Search the red black tree for a fit */
	if ((bp = find_fit_in_tree(asize)) != NULL) {
		place(bp, asize);
	//printf("\n malloc out check: return bp: %p\n",bp);
#ifdef checkheap
		mm_checkheap(VERBOSE);
#endif // checkheap
		return bp;
	}

	/* No fit found. Get more memory and place the block */
	/* erase footer*/
	extendsize = MAX(asize, CHUNKSIZE);

	if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {

		return NULL;
	}

	if ((bp = find_fit_in_tree(asize)) != NULL) {
		place(bp, asize);
	//printf("\n malloc out check: return bp: %p\n",bp);
#ifdef checkheap
		mm_checkheap(VERBOSE);
#endif // checkheap
		
		return bp;
	}

}
/* $end mmmalloc */

/*
* mm_free - Free a block
*/
/* $begin mmfree */
void mm_free(void *bp)
{
	//printf("\nfree in: free count: %d\n",free_call_count++);
	size_t size = GET_SIZE(HDRP(bp));

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));

	coalesce(bp);
#ifdef checkheap
	mm_checkheap(VERBOSE);
#endif // checkheap

}

/* $end mmfree */

/*
* mm_realloc - naive implementation of mm_realloc
*/
void *mm_realloc(void *ptr, size_t size)
{
	
	void *newp;
	size_t copySize;
	copySize = GET_SIZE(HDRP(ptr));
	
	if ((newp = mm_malloc(size)) == NULL) {
		printf("ERROR: mm_malloc failed in mm_realloc\n");
		exit(1);
	}
	
	if (size < copySize)
		copySize = size;
	memcpy(newp, ptr, copySize);
	mm_free(ptr);
	return newp;
}

/*
* mm_checkheap - Check the heap for consistency
*/
void mm_checkheap(int verbose)
{
	char *bp = heap_listp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if ((GET_SIZE(HDRP(heap_listp)) != 4 * DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header, size=%d, alloc=%d\n", GET_SIZE(HDRP(heap_listp)), GET_ALLOC(HDRP(heap_listp)));
	checkblock(heap_listp);
	printblock(heap_listp);
	printf("\nmemory:\n");
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
#ifdef printalloc
	if(verbose)
		printblock(bp);
#endif	
#ifndef printalloc	
	if (verbose && !GET_ALLOC(HDRP(bp)))
		printblock(bp);
#endif		
		
	checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp))){
		printf("Bad epilogue header, size=%d, alloc=%d\n", GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
		exit(2);	
	}
}

/* The remaining routines are internal helper routines */

/*
* extend_heap - Extend heap with free block and return its block pointer
*/
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
	
	char *bp;
	size_t size;
	//heap_end = mem_heap_hi();
	//printf("\nextend_heap in\n");
	
	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));         /* free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

										  //printf("\nextend_heap out\n");
										  /* Coalesce if the previous block was free */
	return coalesce(bp);

}
/* $end mmextendheap */

/*
* place - Place block of asize bytes at start of free block bp
*         and split if reminder would be at least minimum block size
*/
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize) {
#ifdef printre
	printf("\nplace in: place size: %d, bp: %p\n",asize,bp);
#endif // printre	
#ifdef checkheap
	mm_checkheap(VERBOSE);
#endif // checkheap
	size_t csize = GET_SIZE(HDRP(bp));

	if ((csize - asize) >= (DSIZE + POINTER_OVERHEAD + OVERHEAD)) {
#ifdef printre
	printf("\nplace in case 1\n");
#endif // printre
		//bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(asize+DSIZE, 1));
		PUT(FTRP(bp), PACK(asize+DSIZE, 1));
		//printf("\nplace in case 1: bp=%p\n",bp);
		bp = NEXT_BLKP(bp);
		//printf("\nplace in case 1: bp=%p\n",bp);		
		
		PUT(HDRP(bp), PACK(csize - asize-DSIZE, 0));
		PUT(FTRP(bp), PACK(csize - asize-DSIZE, 0));
		//printblock(bp);
	//	printf("\nplace in case 1, insert bp: %p\n",bp);
		
		tree_insert(bp);
	}
	else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
#ifdef printre
	printf("\nplace out\n");
#endif // printre
#ifdef checkheap
	mm_checkheap(VERBOSE);
#endif // checkheap
}
/* $end mmplace */





/*
*
*/
static void *find_fit_in_tree(size_t asize)
{
#ifdef printre
	printf("\nfind_fit_in_tree in: ask for asize: %d\n", asize);
#endif // printre
#ifdef checkheap
		mm_checkheap(VERBOSE);
#endif // checkheap
	block_t* bp;
	block_t* temp = NULL;
	bp = PARENT_BLK(heap_listp);
	//printf("\nbp: %p\n",bp);
	while (bp != NULL) {
		if (GET_SIZE(HDRP(bp)) < asize) {

			//printf("\nfind_fit_in_tree in: case 1, bp right=%p\n", RIGHT_BLKP(bp));
			bp = RIGHT_BLK(bp);
			continue;
		}

		if (GET_SIZE(HDRP(bp)) == asize) {
	//		printf("\nfind_fit_in_tree in: case 2\n");
			temp = bp;
			tree_delete(temp);

			return temp;
		}

		else {
	//		printf("\nfind_fit_in_tree in: case 3\n");
			temp = bp;
			if (bp != NULL) {
				bp = LEFT_BLK(bp);
				continue;
			}
			else
				break;

		}
	}
#ifdef printre
	printf("\ntemp: %p\n", temp);
#endif // printre

	if (temp != NULL){

		tree_delete(temp);
		//printf("\nafter delete: temp: %p\n", temp);
#ifdef checkheap
		mm_checkheap(VERBOSE);
#endif // checkheap
		//printblock(temp);
	}
#ifdef printre
	printf("\nfind_fit_in_tree out\n");
#endif // printre
	//printf("\nfind_fit_in_tree out\n");
	return temp; /* no fit */

}

/*
* coalesce - boundary tag coalescing. Return ptr to coalesced block
*/
static void *coalesce(void *bp)
{
	//printf("\ncoalesce in\n");
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
#ifdef checkheap
	mm_checkheap(VERBOSE);
#endif // checkheap

	if (prev_alloc&&next_alloc) {
#ifdef printre
	printf("\ncoalesece case 1 out\n");
#endif // printre
		tree_insert(bp);
#ifdef printre
	printf("\ncoalesece case 1 out\n");
#endif // printre
		
#ifdef checkheap
		mm_checkheap(VERBOSE);
#endif // checkheap
		return bp;
	}

	else if (prev_alloc && !next_alloc) {
#ifdef printre
	printf("\ncoalesece case 2 in\n");
#endif // printre
		tree_delete(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		tree_insert(bp);
#ifdef printre
	printf("\ncoalesece case 2 out\n");
#endif // printre
	}
	else if (!prev_alloc && next_alloc) {
#ifdef printre
		printf("\ncoalesece case 3 in\n");
#endif // printre
	
		tree_delete(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		tree_insert(bp);
#ifdef printre
	printf("\ncoalesece case 3 out\n");
#endif // printre
	}
	else {
#ifdef printre
	printf("\ncoalesece case 4 in\n");
#endif // printre	
		tree_delete(NEXT_BLKP(bp));
		tree_delete(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		tree_insert(bp);
#ifdef printre
	printf("\ncoalesece case 4 out\n");
#endif // printre	
	}
	return bp;
}

/*
* red black tree part begin
*/


/*
* tree insert
* bp is free block pointer.
*/
static void tree_insert(block_t* bp) {
	PUT(HDRP(bp), PACK(GET_SIZE_ALLOC(HDRP(bp)), RED << 1));
	PUT(FTRP(bp), PACK(GET_SIZE_ALLOC(FTRP(bp)), RED << 1));
	block_t*  x = GET_ADDRESS(heap_listp);
	x = *x;
	block_t*  y = NULL;

	while ((x) != NULL) {

		y = x;
		//	printf("\n in while: y=%p,x=%p,x left=%p,x right=%p\n", (char*)y, (char*)x, (char*)LEFT_BLK(x), (char*)LEFT_BLK(x));
		if (GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(x)))
			x = LEFT_BLK(x);
		else
			x = RIGHT_BLK(x);
	}
	//printf("\nout of while: x=%p, bp=%p, y=%p\n",(char*)x,(char*)bp,(char*)y);

	PARENT_BLK(bp) = y;
	//pt();
	if (y == NULL) {

		PUT_ADDRESS(heap_listp, bp);
	}
	else {
		//	printf("\ny left=%p, y right=%p, bp=%p\n", LEFT_BLKP(y), RIGHT_BLKP(y), bp);
		if (GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(y)))
			PUT_ADDRESS(LEFT_BLKP(y), bp);
		else
			PUT_ADDRESS(RIGHT_BLKP(y), bp);

	}
	PUT_ADDRESS(LEFT_BLKP(bp), 0);
	PUT_ADDRESS(RIGHT_BLKP(bp), 0);
	PUT(HDRP(bp), PACK(GET_SIZE_ALLOC(HDRP(bp)), RED << 1));
	PUT(FTRP(bp), PACK(GET_SIZE_ALLOC(FTRP(bp)), RED << 1));
	//pt();
	insert_fixup(bp);
	return;
}

static void tree_delete(block_t *z) {
	block_t* y = z;
	block_t*par = NULL;
	block_t* x = NULL;
	int yoc;
	yoc = IS_RED(y);
	if (LEFT_BLK(z) == NULL) {
		x = RIGHT_BLK(z);
		par = PARENT_BLK(z);
		transplant(z, RIGHT_BLK(z));
	}
	else if (RIGHT_BLK(z) == NULL) {
		par = PARENT_BLK(z);
		x = LEFT_BLK(z);
		transplant(z, LEFT_BLK(z));

	}
	else {
		y = minimum(RIGHT_BLK(z));
		yoc = IS_RED(y);
		x = RIGHT_BLK(y);
		if (z == PARENT_BLK(y)) {
			if (x != NULL)
				PUT_ADDRESS(PARENT_BLKP(x), y);
			par = y;
		}
		else {
			transplant(y, RIGHT_BLK(y));
			par = PARENT_BLK(y);
			PUT_ADDRESS(RIGHT_BLKP(y), RIGHT_BLK(z));
			PUT_ADDRESS(PARENT_BLKP(RIGHT_BLK(y)), y);

		}
		transplant(z, y);
		PUT_ADDRESS(LEFT_BLKP(y), LEFT_BLK(z));
		PUT_ADDRESS(PARENT_BLKP(LEFT_BLK(y)), y);
		PUT(HDRP(y), PACK(GET_SIZE_ALLOC(HDRP(y)), IS_RED(z) << 1));
		PUT(FTRP(y), PACK(GET_SIZE_ALLOC(FTRP(y)), IS_RED(z) << 1));
	}
	//printf("\ndelete out\n");

	if (yoc == BLACK) {
		//printf("\ndelete fixup\n");

		//pt();
		//printf("\ndelete fix up in. x=%p\n", (char*)x);
		delete_fixup(x, par);

	}
	return;
}

static void right_rotate(block_t* bp) {
	block_t* x = NULL;
	x = LEFT_BLK(bp);
	PUT_ADDRESS(LEFT_BLKP(bp), RIGHT_BLK(x));
	if (RIGHT_BLK(x) != NULL)
		PUT_ADDRESS(PARENT_BLKP(RIGHT_BLK(x)), bp);
	PUT_ADDRESS(PARENT_BLKP(x), PARENT_BLK(bp));
	if (PARENT_BLK(bp) == NULL)
		PUT_ADDRESS(heap_listp, x);
	else {
		if (bp == RIGHT_BLK(PARENT_BLK(bp)))
			PUT_ADDRESS(RIGHT_BLKP(PARENT_BLK(bp)), x);
		else
			PUT_ADDRESS(LEFT_BLKP(PARENT_BLK(bp)), x);
	}
	PUT_ADDRESS(RIGHT_BLKP(x), bp);
	PUT_ADDRESS(PARENT_BLKP(bp), x);
	return;
}
static void left_rotate(block_t *bp) {
	block_t* y = NULL;
	y = RIGHT_BLK(bp);
	PUT_ADDRESS(RIGHT_BLKP(bp), LEFT_BLK(y));
	if (LEFT_BLK(y) != NULL) {
		PUT_ADDRESS(PARENT_BLKP(LEFT_BLK(y)), bp);
	}
	PUT_ADDRESS(PARENT_BLKP(y), PARENT_BLK(bp));
	if (PARENT_BLK(bp) == NULL) {
		PUT_ADDRESS(heap_listp, y);
	}
	else {
		if (bp == LEFT_BLK(PARENT_BLK(bp))) {
			PUT_ADDRESS(LEFT_BLKP(PARENT_BLK(bp)), y);
		}
		else {
			PUT_ADDRESS(RIGHT_BLKP(PARENT_BLK(bp)), y);
		}
	}
	PUT_ADDRESS(LEFT_BLKP(y), bp);
	PUT_ADDRESS(PARENT_BLKP(bp), y);

	return;
}

static void transplant(block_t* u, block_t* v) {
	if (PARENT_BLK(u) == NULL) {
		PUT_ADDRESS(heap_listp, v);

	}
	else if (u == LEFT_BLK(PARENT_BLK(u))) {
		//printf("\ntransplant case 2: left=%p,*v=%p\n", (char*)*(LEFT_BLKP(PARENT_BLKP(u))), (char*)*v);
		PUT_ADDRESS((LEFT_BLKP(PARENT_BLK(u))), v);

	}
	else {
		//printf("\ntransplant case 3:\n");
		PUT_ADDRESS((RIGHT_BLKP(PARENT_BLK(u))), v);

		//printblock(v,1);
	}
	if (v != NULL) {
		//printf("\nbreak point 1: target=%p,v parent=%p\n", (char*)*u, (char*)(*(char*)(PARENT_BLKP(v))));
		//pt();
		PUT_ADDRESS(PARENT_BLKP(v), PARENT_BLK(u));
		//pt();
	}

	//printf("\ntransplant out\n");

	return;
}

static block_t* minimum(block_t *bp) {
	//printf("\nminimum in\n");
	//bp=PARENT_BLK(bp);
	//printf("\nbreak point 1: bp=%p,bp left=%p\n", (char*)bp, (char*)LEFT_BLK(bp));
	while (LEFT_BLK(bp) != NULL)
		bp = LEFT_BLK(bp);
	//printf("\nminimum out: bp=%p\n", (char*)bp);
	return bp;
}

static void delete_fixup(block_t * x, block_t *par) {
	block_t* w = NULL;
	while (x != PARENT_BLK(heap_listp) && (x == NULL || !IS_RED(x))) {

		if (x == LEFT_BLK(par)) {
			w = RIGHT_BLK(par);
			if (w != NULL && IS_RED(w)) {
				PUT(HDRP(w), PACK(GET_SIZE_ALLOC(HDRP(w)), BLACK << 1));
				PUT(FTRP(w), PACK(GET_SIZE_ALLOC(FTRP(w)), BLACK << 1));
				PUT(HDRP(par), PACK(GET_SIZE_ALLOC(HDRP((par))), RED << 1));
				PUT(FTRP(par), PACK(GET_SIZE_ALLOC(FTRP((par))), RED << 1));
				left_rotate(par);
				w = RIGHT_BLK(par);
			}

			if ((RIGHT_BLK(w) == NULL || !IS_RED(RIGHT_BLK(w))) && (LEFT_BLK(w) == NULL || !IS_RED(LEFT_BLK(w)))) {
				PUT(HDRP(w), PACK(GET_SIZE_ALLOC(HDRP(w)), RED << 1));
				PUT(FTRP(w), PACK(GET_SIZE_ALLOC(FTRP(w)), RED << 1));
				x = par;
				par = PARENT_BLK(par);
			}

			else {
				if (RIGHT_BLK(w) == NULL || !IS_RED(RIGHT_BLK(w))) {
					PUT(HDRP(LEFT_BLK(w)), PACK(GET_SIZE_ALLOC(HDRP(LEFT_BLK(w))), BLACK << 1));
					PUT(FTRP(LEFT_BLK(w)), PACK(GET_SIZE_ALLOC(FTRP(LEFT_BLK(w))), BLACK << 1));
					PUT(HDRP(w), PACK(GET_SIZE_ALLOC(HDRP(w)), RED << 1));
					PUT(FTRP(w), PACK(GET_SIZE_ALLOC(FTRP(w)), RED << 1));
					right_rotate(w);
					w = RIGHT_BLK(par);
				}
				PUT(HDRP(w), PACK(GET_SIZE_ALLOC(HDRP(w)), IS_RED(par) << 1));
				PUT(FTRP(w), PACK(GET_SIZE_ALLOC(FTRP(w)), IS_RED(par) << 1));
				PUT(HDRP(par), PACK(GET_SIZE_ALLOC(HDRP(par)), BLACK << 1));
				PUT(FTRP(par), PACK(GET_SIZE_ALLOC(FTRP(par)), BLACK << 1));
				PUT(HDRP(RIGHT_BLK(w)), PACK(GET_SIZE_ALLOC(HDRP(RIGHT_BLK(w))), BLACK << 1));
				PUT(FTRP(RIGHT_BLK(w)), PACK(GET_SIZE_ALLOC(FTRP(RIGHT_BLK(w))), BLACK << 1));
				left_rotate(par);
				x = PARENT_BLK(heap_listp);
			}
		}
		else {
			w = LEFT_BLK(par);
			if (w != NULL && IS_RED(w)) {
				PUT(HDRP(w), PACK(GET_SIZE_ALLOC(HDRP(w)), BLACK << 1));
				PUT(FTRP(w), PACK(GET_SIZE_ALLOC(FTRP(w)), BLACK << 1));
				PUT(HDRP(par), PACK(GET_SIZE_ALLOC(HDRP((par))), RED << 1));
				PUT(FTRP(par), PACK(GET_SIZE_ALLOC(FTRP((par))), RED << 1));
				right_rotate(par);
				w = LEFT_BLK(par);
			}

			if ((RIGHT_BLK(w) == NULL || !IS_RED(RIGHT_BLK(w))) && (LEFT_BLK(w) == NULL || !IS_RED(LEFT_BLK(w)))) {
				PUT(HDRP(w), PACK(GET_SIZE_ALLOC(HDRP(w)), RED << 1));
				PUT(FTRP(w), PACK(GET_SIZE_ALLOC(FTRP(w)), RED << 1));
				x = par;
				par = PARENT_BLK(par);
			}
			else {
				if (LEFT_BLK(w) == NULL || !IS_RED(LEFT_BLK(w))) {
					PUT(HDRP(RIGHT_BLK(w)), PACK(GET_SIZE_ALLOC(HDRP(RIGHT_BLK(w))), BLACK << 1));
					PUT(FTRP(RIGHT_BLK(w)), PACK(GET_SIZE_ALLOC(FTRP(RIGHT_BLK(w))), BLACK << 1));
					PUT(HDRP(w), PACK(GET_SIZE_ALLOC(HDRP(w)), RED << 1));
					PUT(FTRP(w), PACK(GET_SIZE_ALLOC(FTRP(w)), RED << 1));
					left_rotate(w);
					w = LEFT_BLK(par);
				}
				PUT(HDRP(w), PACK(GET_SIZE_ALLOC(HDRP(w)), IS_RED(par) << 1));
				PUT(FTRP(w), PACK(GET_SIZE_ALLOC(FTRP(w)), IS_RED(par) << 1));
				PUT(HDRP(par), PACK(GET_SIZE_ALLOC(HDRP(par)), BLACK << 1));
				PUT(FTRP(par), PACK(GET_SIZE_ALLOC(FTRP(par)), BLACK << 1));
				PUT(HDRP(LEFT_BLK(w)), PACK(GET_SIZE_ALLOC(HDRP(LEFT_BLK(w))), BLACK << 1));
				PUT(FTRP(LEFT_BLK(w)), PACK(GET_SIZE_ALLOC(FTRP(LEFT_BLK(w))), BLACK << 1));
				right_rotate(par);
				x = PARENT_BLK(heap_listp);
			}
		}
	}
	if (x != NULL) {
		PUT(HDRP(x), PACK(GET_SIZE_ALLOC(HDRP(x)), BLACK << 1));
		PUT(FTRP(x), PACK(GET_SIZE_ALLOC(FTRP(x)), BLACK << 1));
	}
	return;
}



static void insert_fixup(block_t* bp) {

	block_t* y = NULL;

	while (PARENT_BLK(bp) && IS_RED(PARENT_BLK(bp))) {
		if (PARENT_BLK(bp) == LEFT_BLK(PARENT_BLK(PARENT_BLK(bp)))) {
			y = (char*)RIGHT_BLK(PARENT_BLK(PARENT_BLK(bp)));

			if (y != NULL && IS_RED(y)) {
				PUT(HDRP(PARENT_BLK(bp)), PACK(GET_SIZE_ALLOC(HDRP((PARENT_BLK(bp)))), BLACK << 1));
				PUT(FTRP(PARENT_BLK(bp)), PACK(GET_SIZE_ALLOC(FTRP((PARENT_BLK(bp)))), BLACK << 1));
				PUT(HDRP(y), PACK(GET_SIZE_ALLOC(HDRP(y)), BLACK << 1));
				PUT(FTRP(y), PACK(GET_SIZE_ALLOC(FTRP(y)), BLACK << 1));
				PUT(HDRP(PARENT_BLK(PARENT_BLK(bp))), PACK(GET_SIZE_ALLOC(HDRP(PARENT_BLK(PARENT_BLK(bp)))), RED << 1));
				PUT(FTRP(PARENT_BLK(PARENT_BLK(bp))), PACK(GET_SIZE_ALLOC(FTRP(PARENT_BLK(PARENT_BLK(bp)))), RED << 1));
				bp = PARENT_BLK(PARENT_BLK(bp));
			}
			else {
				if (bp == RIGHT_BLK(PARENT_BLK(bp))) {
					bp = PARENT_BLK(bp);
					left_rotate(bp);
				}
				PUT(HDRP(PARENT_BLK(bp)), PACK(GET_SIZE_ALLOC(HDRP((PARENT_BLK(bp)))), BLACK << 1));
				PUT(FTRP(PARENT_BLK(bp)), PACK(GET_SIZE_ALLOC(FTRP((PARENT_BLK(bp)))), BLACK << 1));
				PUT(HDRP(PARENT_BLK(PARENT_BLK(bp))), PACK(GET_SIZE_ALLOC(HDRP(PARENT_BLK(PARENT_BLK(bp)))), RED << 1));
				PUT(FTRP(PARENT_BLK(PARENT_BLK(bp))), PACK(GET_SIZE_ALLOC(FTRP(PARENT_BLK(PARENT_BLK(bp)))), RED << 1));
				right_rotate(PARENT_BLK(PARENT_BLK(bp)));

			}
		}

		else {
			y = (char*)LEFT_BLK(PARENT_BLK(PARENT_BLK(bp)));
			if (y != NULL && IS_RED(y)) {
				PUT(HDRP(PARENT_BLK(bp)), PACK(GET_SIZE_ALLOC(HDRP((PARENT_BLK(bp)))), BLACK << 1));
				PUT(FTRP(PARENT_BLK(bp)), PACK(GET_SIZE_ALLOC(FTRP((PARENT_BLK(bp)))), BLACK << 1));
				PUT(HDRP(y), PACK(GET_SIZE_ALLOC(HDRP(y)), BLACK << 1));
				PUT(FTRP(y), PACK(GET_SIZE_ALLOC(FTRP(y)), BLACK << 1));
				PUT(HDRP(PARENT_BLK(PARENT_BLK(bp))), PACK(GET_SIZE_ALLOC(HDRP(PARENT_BLK(PARENT_BLK(bp)))), RED << 1));
				PUT(FTRP(PARENT_BLK(PARENT_BLK(bp))), PACK(GET_SIZE_ALLOC(FTRP(PARENT_BLK(PARENT_BLK(bp)))), RED << 1));
				bp = PARENT_BLK(PARENT_BLK(bp));
			}
			else {
				if (bp == LEFT_BLK(PARENT_BLK(bp))) {
					bp = PARENT_BLK(bp);
					right_rotate(bp);
				}
				PUT(HDRP(PARENT_BLK(bp)), PACK(GET_SIZE_ALLOC(HDRP((PARENT_BLK(bp)))), BLACK << 1));
				PUT(FTRP(PARENT_BLK(bp)), PACK(GET_SIZE_ALLOC(FTRP((PARENT_BLK(bp)))), BLACK << 1));
				PUT(HDRP(PARENT_BLK(PARENT_BLK(bp))), PACK(GET_SIZE_ALLOC(HDRP(PARENT_BLK(PARENT_BLK(bp)))), RED << 1));
				PUT(FTRP(PARENT_BLK(PARENT_BLK(bp))), PACK(GET_SIZE_ALLOC(FTRP(PARENT_BLK(PARENT_BLK(bp)))), RED << 1));
				left_rotate(PARENT_BLK(PARENT_BLK(bp)));
			}
		}
	}
	PUT(HDRP(PARENT_BLK(heap_listp)), PACK(GET_SIZE_ALLOC(HDRP(PARENT_BLK((heap_listp)))), BLACK << 1));
	PUT(FTRP(PARENT_BLK(heap_listp)), PACK(GET_SIZE_ALLOC(FTRP(PARENT_BLK((heap_listp)))), BLACK << 1));
	return;
}

static void printblock(void *bp)
{
	size_t hsize, halloc, fsize, falloc;

	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	if (hsize == 0) {
		printf("%p: EOL\n", bp);
		return;
	}

	printf("%p: header: [%d:%c] footer: [%d:%c] color: %d, prev: %p, next: %p, parent: %p, left: %p, right: %p\n", bp,
	hsize, (halloc ? 'a' : 'f'),
	fsize, (falloc ? 'a' : 'f'), IS_RED(bp), (char*)PREV_BLKP(bp), (char*)NEXT_BLKP(bp), (char*)PARENT_BLK(bp), (char*)LEFT_BLK(bp), (char*)RIGHT_BLK(bp));
}

static void checkblock(void *bp)
{
	if ((size_t)bp % 8)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET_SIZE_ALLOC(HDRP(bp)) != GET_SIZE_ALLOC(FTRP(bp)))
		printf("Error: header does not match footer: header:%x, footer:%x\n", GET(HDRP(bp)), GET(FTRP(bp)));
}

