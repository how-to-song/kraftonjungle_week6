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
/* ~0x7 = 0xFFFFFFF8 = 111...1000  8의 배수로 올림*/
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// size_t의 크기를 8의 배수로 올림한 크기 SIZE_T_SIZE
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             // 워드 크기 
#define DSIZE 8             // 더블 워드 크기
#define CHUNKSIZE (1<<12)   // 청크 사이즈 2^12 4KB

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// 크기 비트와 할당 비트 OR로 비어있는 크기 비트의 하위 3비트에 할당 비트 추가 = 헤더, 풋터에 넣을거
#define PACK(size, alloc) ((size) | (alloc))

// p주소에 있는 워드 읽기, 쓰기
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 크기, 할당비트 읽기
#define GET_SIZE(p) (GET(p) & ~0x7) // 11...1000으로 뒤에 비트 빼고 크기비트만
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp(페이로드의 시작부분)이 주어지면 그 페이로드의 헤더와 풋터 주소
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음, 이전 블록 위치
// 현재 페이로드에서 워드만큼 빼면 현재 블록 헤더, 현재 헤더가 가지고 있는 사이즈만큼 bp에서 더하기 GET_SIZE(((char *)(bp) - WSIZE)) == GET_SIZE(HDRP(bp))
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 현재 페이로드에서 더블 워드 만큼 빼면 이전 블록의 풋터, 이전 풋터가 가지고 있는 사이즈만큼 bp에서 빼기 
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


static char *heap_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *ptr);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 초기화를 위한 brk포인터 4워드만큼 증가
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) 
        return -1;

    PUT(heap_listp, 0);                                 // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      // 프롤로그의 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      // 프롤로그의 풋터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          // 에필로그의 헤더

    heap_listp += 2 * WSIZE;                            // 시작을 위해 프롤로그의 헤더 다음으로 이동

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;
        
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), 1);

    // 병합
    return coalesce(bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // 원래 있던 함수
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize, extend_size;
    char *bp;

    if (size == 0) return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else 
        asize = DSIZE * ((size + DSIZE + (DSIZE -1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extend_size = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) 
        return NULL;
    
    place(bp, asize);
    return bp;
}

// 해당 주소의 헤더, 풋터 할당 비트 0로 설정
void mm_free(void *ptr)
{
    if (ptr == NULL) return;

    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    // 병합
    coalesce(ptr);
}

static void *coalesce(void *ptr) {
    int prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    // 이전 블록, 다음 블록 다 할당되어 있을 때
    if (prev_alloc && next_alloc) {
        return ptr;
    }
    // 이전 블록은 할당, 다음 블록은 가용
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    // 이전 블록은 가용, 다음 블록 할당
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    // 이전 블록, 다음 블록 둘 다 가용
    else if (!prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)))
                + GET_SIZE(HDRP(PREV_BLKP(ptr)));

        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    return ptr;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}