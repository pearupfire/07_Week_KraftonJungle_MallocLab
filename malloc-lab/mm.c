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



#define WSIZE 4 // 1 word = 4 byte (헤더와 풋터의 크기)
#define DSIZE 8 // 2 word = 8 byte (블록의 최소 크기 정렬 기준 8 byte 이상)
#define CHUNKSIZE (1<<12) // 2^12 -> 4096 byte -> 4kb (초기 힙을 얼마나 크게 확장할지 정하는 상수)

/* 최대값 매크로
 * (x, y) 중 큰 값 반환
 */ 
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 패킹 메크로
 * size와 alloc 값을 비트 연산으로 합쳐 하나의 4바이트 워드에 저장
 * size : 블록의 전체 크기 (haeder, payload, footer)
 * alloc : 블록의 할당 여부 (0 = free, 1 = allocated)
 */
#define PACK(size, alloc) ((size) | (alloc))    

/* 읽기 / 쓰기 매크로
 * GET(p)       : 주어진 주소에서 4 byte (unsigned int)를 읽기
 * PUT(p, val)  : 주어진 주소에 4 byte (unsigned int)로 val 값을 쓰기 
 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 블록의 크기 / 할당 여부 추출 매크로
 * GET_SIZE(p) : p의 주소에서 블록의 크기 추출
 * GET_ALLOC(p) : p의 주소에서 블록의 할당 여부 추출
 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 헤더와 풋터의 주소를 반환하는 매크로
 * HDRP(bp) : 블록 포인터(bp)에서 헤더 주소를 반환하는 매크로
 * FTRP(bp) : 블록 포인터(bp)에서 풋터 주소를 반환하는 매크로
 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 현재 블록 포인터 bp로 부터 다음 / 이전 블록 포인터를 계산하는 메크로
 * NEXT_BLKP(bp) : 다음 블록 포인터 매크로
 * PREV_BLKP(bp) : 이전 블록 포인터 매크로
 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;

static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

/*
 * mm_init - initialize the malloc package.
 */

 /// @brief malloc 초기화 함수
 /// @return 성공 시 0, 실패 시 -1
 int mm_init(void)
{
    // 초기 힙 영역을 4개의 워드로 요청 -> [padding][prologue header][prologue footer][epilogue header]
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1; // 실패 시 -1 반환
    
    // 힙의 시작 위치에 4개의 워드 세팅
    PUT(heap_listp, 0);                            // padding word
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0,1));      // epilogue haeder
    heap_listp += (2 * WSIZE); // 힙 포인터 prologue block의 payload 시작 위치로 이동

    // 초기 가용 블록을 만들기 위해 힙을 CHUNKSIZE 만큼 확장
    // CHUNKSUZE / WSIZE = 4096 / 4 = 1024 words
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1; // 실패 시 -1
    
    return 0; // 성공 시 0
}

/// @brief 힙을 word 단위로 확장하고 새로운 가용 블록 생성
/// @param words 확장할 크기 (word 단위)
/// @return 새로 생성된 가용 블록의 포인터, 실패 시 NULL
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 짝수 워드 단위로 정렬 (8바이트 정렬 보장 위해)
    //  홀수면 1워드 추가해서 짝수로 바꿈
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 메모리에서 size 만큼 힙을 확장
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL; // 실패 시 NULL 반환
    
    // 새로 생성된 block에 header / footer 설정 (free block)
    PUT(HDRP(bp), PACK(size, 0)); // 새 block의 header
    PUT(FTRP(bp), PACK(size, 0)); // 새 block의 footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 epilogue header 생성
    
    // 이전 가용 블록과 연결하여 병합한 후 변환
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { 
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

// void *mm_malloc(size_t size)
// {
//     int newsize = ALIGN(size + SIZE_T_SIZE);
//     void *p = mem_sbrk(newsize);
//     if (p == (void *)-1)
//         return NULL;
//     else
//     {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
        
    place(bp, asize);

    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;

    
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

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
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