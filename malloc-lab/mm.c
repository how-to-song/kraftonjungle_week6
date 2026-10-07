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
#define PSIZE 8             // 포인터 사이즈
#define CHUNKSIZE (1<<12)   // 청크 사이즈 2^12 4KB
#define MIN_BLK_SIZE (3 * DSIZE) // 최소 블록 사이즈 why? 헤더+풋터 DSIZE(8바이트), pred포인터(8바이트), succ포인터(8바이트)
#define LISTLIMIT 20        // 분리 가용 리스트 최대 개수

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

// 크기 비트와 할당 비트 OR로 비어있는 크기 비트의 하위 3비트에 할당 비트 추가 = 헤더, 풋터에 넣을거
#define PACK(size, alloc) ((size) | (alloc))

// p주소에 있는 워드 읽기, 쓰기
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 크기, 할당비트 읽기
#define GET_SIZE(p) (GET(p) & ~0x7) // 11...1000으로 뒤에 비트 빼고 크기비트만
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp(페이로드의 시작부분)이 주어지면 그 블록의 헤더와 풋터 주소
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음, 이전 블록 위치
// 현재 페이로드에서 워드만큼 빼면 현재 블록 헤더, 현재 헤더가 가지고 있는 사이즈만큼 bp에서 더하기 GET_SIZE(((char *)(bp) - WSIZE)) == GET_SIZE(HDRP(bp))
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 현재 페이로드에서 더블 워드 만큼 빼면 이전 블록의 풋터, 이전 풋터가 가지고 있는 사이즈만큼 bp에서 빼기 
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// pred, succ 포인터가 있는 곳의 주소
#define PRED(bp) ((void **)(bp))
#define SUCC(bp) ((void **)((char *)(bp) + PSIZE))
// 포인터 읽기, 쓰기
#define GET_P(ptr) (*(ptr))
#define PUT_P(ptr, val) ((*(ptr)) = (val))

// 힙을 주소순으로 읽을 때 포인터
static char *heap_listp;
// 힙의 가용 블록을 읽을 때 포인터
// static char *heap_free_listp;
// 크기 클래스별 분리 가용 리스트
static void *segregated_free_list[LISTLIMIT];

// 크기별 분리 가용리스트 인덱스 구하기
static int get_idx_sc(size_t size) {
    size = (size - MIN_BLK_SIZE) / DSIZE;
    int list_idx = 0;

    while ((list_idx < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list_idx++;
    }
    
    return list_idx;
}

static size_t cal_asize(size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static void *split(void *bp, size_t asize);
static void insert_fblk(void *bp);
static void remove_fblk(void *bp);


// #define DEBUG   // 디버깅할 때만 이 줄의 주석을 푼다
#ifdef DEBUG
static char *broken_heap_ptr;
// bp 불변식 검사 1: 정상 / -1: 블록이 힙 범위 밖, -2: 블록 크기 이상, -3: 헤더, 풋터 다름
//                        -4: 인접한 가용 블록, -5: 8배수 정렬 이상, -6: 블록이 맞지 않은 클래스에 있음, -7: 가용 블록 수 다름
static int mm_checkheap(void) {
    char *curr = NEXT_BLKP(heap_listp);
    int free_count_h = 0;
    int free_count_s = 0;
    // 프롤로그 다음 블록 부터 에필로그
    while (curr - 1 != mem_heap_hi()){
        broken_heap_ptr = curr;
        // 블록이 힙 범위 안에 있는지
        if ((long)curr < (long)mem_heap_lo() || (long)curr > (long)mem_heap_hi()) return -1;
        // 블록의 크기가 정확
        if (GET_SIZE(HDRP(curr)) < MIN_BLK_SIZE || (long)FTRP(curr) > (long)((char *)mem_heap_hi() - (DSIZE - 1)))return -2;
        // 헤더, 풋터 동일
        if (GET(HDRP(curr)) != GET(FTRP(curr))) return -3;
        // 인접한 가용 블록
        if (!GET_ALLOC(HDRP(curr)) && (!GET_ALLOC(HDRP(NEXT_BLKP(curr))))) return -4;
        // 8배수 정렬
        if ((long)curr % 8 != 0) return -5;
        // 가용 블록 개수 더하기
        if (!GET_ALLOC(HDRP(curr))) free_count_h++;

        curr = NEXT_BLKP(curr);
    }

    for (int i = 0; i < LISTLIMIT; i++) {
        curr = segregated_free_list[i];
        while (curr != NULL && free_count_s <= free_count_h) {
            broken_heap_ptr = curr;
            if (get_idx_sc(GET_SIZE(HDRP(curr))) != i) return -6;
            free_count_s++;
            curr = GET_P(SUCC(curr));
        }
    }

    broken_heap_ptr = NULL;
    // 가용 블록의 수가 다르다.
    if (free_count_h != free_count_s) return -7;

    // 정상
    return 1;
}

#define CHECKHEAP() do {                                                   \
        int r = mm_checkheap();                                            \
        if (r != 1) {                                                      \
            fprintf(stderr, "[checkheap] %s:%d code=%d bp=%p\n",           \
                    __func__, __LINE__, r, (void *)broken_heap_ptr);       \
            if (r != -1 && r != -7)                                                   \
                fprintf(stderr, "  header=0x%x\n", GET(HDRP(broken_heap_ptr))); \
            assert(0);                                                     \
        }                                                                  \
    } while (0)
#else
#define CHECKHEAP()
#endif


// 요청한 크기에 맞는 블록 크기 계산
static size_t cal_asize(size_t size) {
    size_t asize;

    if (size <= MIN_BLK_SIZE - DSIZE)
        asize = MIN_BLK_SIZE;
    else 
        asize = DSIZE * ((size + DSIZE + (DSIZE -1)) / DSIZE);

    return asize;
}

static void insert_fblk(void *bp) {
    // 단일 가용 리스트
    // 가용 리스트 포인터가 NULL이면 첫 가용 블록
    // if (heap_free_listp == NULL) {
    //     PUT_P(PRED(bp), NULL);
    //     PUT_P(SUCC(bp), NULL);
    // }
    // else {
    //     PUT_P(PRED(heap_free_listp), bp);
    //     PUT_P(SUCC(bp), heap_free_listp);
    //     PUT_P(PRED(bp), NULL);
    // }

    // heap_free_listp = bp;


    int list_idx = get_idx_sc(GET_SIZE(HDRP(bp)));
    if (!segregated_free_list[list_idx]) {
        PUT_P(PRED(bp), NULL);
        PUT_P(SUCC(bp), NULL);
    }
    else {
        PUT_P(PRED(segregated_free_list[list_idx]), bp);
        PUT_P(SUCC(bp), segregated_free_list[list_idx]);
        PUT_P(PRED(bp), NULL);
    }

    segregated_free_list[list_idx] = bp;
}

static void remove_fblk(void *bp) {
    int list_idx = get_idx_sc(GET_SIZE(HDRP(bp)));

    if (!GET_P(PRED(bp)) && !GET_P(SUCC(bp))) {
        segregated_free_list[list_idx] = NULL;
    }
    // 시작
    else if(!GET_P(PRED(bp)) && GET_P(SUCC(bp))) {
        segregated_free_list[list_idx] = GET_P(SUCC(bp));
        PUT_P(PRED(GET_P(SUCC(bp))), NULL);
    }
    // 마지막
    else if (GET_P(PRED(bp)) && !GET_P(SUCC(bp))) {
        PUT_P(SUCC(GET_P(PRED(bp))), NULL);
    }
    // 중간
    else {
        PUT_P(SUCC(GET_P(PRED(bp))), GET_P(SUCC(bp)));
        PUT_P(PRED(GET_P(SUCC(bp))), GET_P(PRED(bp)));
    }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 초기화를 위한 brk포인터 4워드만큼 증가
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) 
        return -1;

    // 단일 연결 리스트
    //heap_free_listp = NULL;

    // 분리 가용 리스트
    for (int i = 0; i < LISTLIMIT; i++) {
        segregated_free_list[i] = NULL;
    }

    PUT(heap_listp, 0);                                 // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      // 프롤로그의 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      // 프롤로그의 풋터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          // 에필로그의 헤더

    heap_listp += 2 * WSIZE;                            // 시작을 위해 프롤로그의 헤더 다음으로 이동

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words) {
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

    asize = cal_asize(size);

    if ((bp = find_fit(asize)) != NULL){
        bp = place(bp, asize);
        CHECKHEAP();
        return bp;
    }

    void *last_blk_f = (char *)mem_heap_hi() - 7;

    if (!GET_ALLOC(last_blk_f)) {
        extend_size = MAX(asize - GET_SIZE(last_blk_f), MIN_BLK_SIZE);
    }
    else {
        extend_size = MAX(asize, CHUNKSIZE);
    }
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) 
        return NULL;
    
    bp = place(bp, asize);
    CHECKHEAP();
    return bp;
}

static void *find_fit(size_t asize) {
    // 단일 연결 리스트
    // char *curr = heap_free_listp;

    // while(curr != NULL) {
    //     // 크기가 인자 asize보다 크거나 같으면 해당 주소 반환
    //     if (GET_SIZE(HDRP(curr)) >= asize) {
    //         break;
    //     }
    //     curr = GET_P(SUCC(curr));
    // }
    // // 찾는데 실패시 NULL 반환
    // return curr;

    // 분리 가용 리스트
    void *bp = NULL;
    int list_idx = get_idx_sc(asize);

    while(list_idx < LISTLIMIT) {
        if (segregated_free_list[list_idx] != NULL) {
            bp = segregated_free_list[list_idx];
            while (bp != NULL && GET_SIZE(HDRP(bp)) < asize) {
                bp = GET_P(SUCC(bp));
            }
            if (bp != NULL) return bp;
        }
        list_idx++;
    }

    return NULL;
}

static void *place(void *bp, size_t asize) {
    // 현재 블록이 할당되어 있거나 크기가 asize보다 작으면 아무것도 안함
    if (GET_ALLOC(HDRP(bp)) || GET_SIZE(HDRP(bp)) < asize) return NULL;

    remove_fblk(bp);
    // 분할
    char *split_bp;
    size_t split_size = GET_SIZE(HDRP(bp)) - asize;

    if ((GET_SIZE(HDRP(bp)) / 2) > asize) {
        PUT(HDRP(bp), PACK(split_size, 0));
        PUT(FTRP(bp), PACK(split_size, 0));

        split_bp = NEXT_BLKP(bp);
        PUT(HDRP(split_bp), PACK(asize, 1));
        PUT(FTRP(split_bp), PACK(asize, 1));

        void *temp = split_bp;
        split_bp = bp;
        bp = temp;

        coalesce(split_bp);
    } else {
        split(bp, asize);
    }

    return bp;
}

static void *split(void *bp, size_t asize) {
    int is_split = 1;
    char *split_bp;
    size_t split_size = GET_SIZE(HDRP(bp)) - asize;
    // 나눴을 때 크기가 최소 블록 사이즈보다 작으면 블록으로써 기능X, 그냥 현재 블록에다 모두 할당
    if (split_size < MIN_BLK_SIZE) {
        asize += split_size;
        is_split = 0;
    }

    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));


    if (is_split) {
        split_bp = NEXT_BLKP(bp);

        PUT(HDRP(split_bp), PACK(split_size, 0));
        PUT(FTRP(split_bp), PACK(split_size, 0));
        coalesce(split_bp);
    }

    return bp;
}

// 해당 주소의 헤더, 풋터 할당 비트 0로 설정
void mm_free(void *bp)
{
    if (bp == NULL) return;

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 병합
    coalesce(bp);
    CHECKHEAP();
}

static void *coalesce(void *bp) {
    int prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 이전 블록, 다음 블록 다 할당되어 있을 때
    if (prev_alloc && next_alloc) {
        //Do Nothing
    }
    // 이전 블록은 할당, 다음 블록은 가용
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_fblk(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // 이전 블록은 가용, 다음 블록 할당
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_fblk(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // 이전 블록, 다음 블록 둘 다 가용
    else if (!prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)))
                + GET_SIZE(HDRP(PREV_BLKP(bp)));

        remove_fblk(PREV_BLKP(bp));
        remove_fblk(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_fblk(bp);
    return bp;
}

// 제자리 최적화 구현
void *mm_realloc(void *bp, size_t size)
{
    // size가 0이면 메모리 해제
    if (!size) {
        mm_free(bp);
        return NULL;
    }

    // realloc(NULL, size) == mm_malloc(size);
    if (!bp) return mm_malloc(size);

    size_t curr_size = GET_SIZE(HDRP(bp));
    size_t asize = cal_asize(size);

    void *oldbp = bp;
    void *newbp = oldbp;
    

    // 수정된 사이즈랑 현재 사이즈랑 같을 때
    if (asize == curr_size) {
        return newbp;
    }

    // 수정된 사이즈가 현재 사이즈 보다 작을 때
    else if(asize < curr_size) {
        split(newbp, asize);
    }

    // 수정된 사이즈가 현재 사이즈 보다 클 때
    else {
        // 해제되어 있으면서 해당 블록의 사이즈랑 현재 사이즈랑 더한 것이 asize보다 크거나 같은가?
        if (!GET_ALLOC(HDRP(NEXT_BLKP(newbp))) && asize <= GET_SIZE(HDRP(NEXT_BLKP(newbp))) + curr_size) {    
            // 다음거랑 병합
            curr_size += GET_SIZE(HDRP(NEXT_BLKP(newbp)));
            remove_fblk(NEXT_BLKP(newbp));
            PUT(HDRP(newbp), PACK(curr_size, 1));
            PUT(FTRP(newbp), PACK(curr_size, 1));

            split(newbp, asize);
        }

        // 둘 중에 하나라도 아니면 새로운 포인터로 재할당
        else {
            // 다음 블록이 에필로그일 때
            if (GET_SIZE(HDRP(NEXT_BLKP(newbp))) == 0) {
                // 다음 블록이 없어서 힙을 더 늘리고
                void* extend = extend_heap((cal_asize(asize - curr_size)) / WSIZE);
                if (!extend) return NULL;
                remove_fblk(extend);

                // 다음 블록과 병합
                curr_size += GET_SIZE(HDRP(NEXT_BLKP(newbp)));
                PUT(HDRP(newbp), PACK(curr_size, 1));
                PUT(FTRP(newbp), PACK(curr_size, 1));

               split(newbp, asize);
            }
            else {
                newbp = mm_malloc(size);
                if (!newbp) return NULL;
            }
        }
    }

    // 값 복사
    // 인자로 받아온 사이즈가 더 작은걸 들고와야 함
    size = MIN(GET_SIZE(HDRP(bp)) - DSIZE, size);
    if (newbp != oldbp) {
        memcpy(newbp, oldbp, size);
        mm_free(oldbp);
    }

    CHECKHEAP();
    return newbp;



    // 옛날 코드
    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //     return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // if (size < copySize)
    //     copySize = size;
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;    
}