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

/// @brief 현재 가용 블록 bp를 기준으로 이전 / 다음 인접한 가용 블록과 병합 함수
/// @param bp 현재 가용 블록 포인터
/// @return 병합 된 가용 블록의 시작 포인터
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태 (이전 footer 에서 확인)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태 (다음 header 에서 확인)
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 크기 

    // case 1 : 이전 다음 모두 할당 되었다면
    if (prev_alloc && next_alloc)
    {
        return bp; // 병합x
    }
    // case 2 : 이전 할당, 다음 가용 -> 현재와 다음 블록 병합
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 사이즈에 다음 블록 사이즈 누적
        PUT(HDRP(bp), PACK(size, 0)); // header / footer 갱신
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case 3 : 이전 가용, 다음 할당 -> 이전과 현재 블록 병합 
    else if (!prev_alloc && next_alloc)
    { 
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 현재 사이즈에 이전 블록 사이즈 누적
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 병합된 footer 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 header 에 병합된 정보 갱신
        bp = PREV_BLKP(bp); // 병합된 블록의 시작 주소를 반환하기 위해 bp 갱신
    }
    // case 4 : 이전 다음 모두 가용 -> 이전 현재 다음 블록 병합
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 현재 사이즈에 이전과 다음 블록을 누적
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 header 에 병합 크기 갱신 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 footer 에 병합 크기 갱신
        bp = PREV_BLKP(bp);
    }

    return bp; // 병합된 가용 블록의 시작 포인터 반환
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

/// @brief size 만큼 heap 에 메모리 블록을 할당하는 함수
/// @param size payload에 핟당할 크기
/// @return 할당된 블록의 포인터, 실패 시 null 반환
void *mm_malloc(size_t size)
{
    size_t asize; // 조정된 블록 크기 
    size_t extendsize; // 힙을 확장해야 할 경우 확장할 크기
    char *bp; // 할당될 블록의 포인터

    if (size == 0) // size가 0인 경우
        return NULL; // NULL 반환
    
    if (size <= DSIZE) // 요청한 size가 최소 블록 크기보다 작다면 (8 byte)
        asize = 2 * DSIZE; // 전체 블록 크기를 16 byte로 설정 (최소 전체 블록의 크기는 16 byte, header 4, payload 8, footer 4)
    else // 8 byte 정렬된 블록 크기 계산
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

        // 적절한 가용 블록을 가용 리스트에서 탐색
    if ((bp = find_fit(asize)) != NULL)
    {
        // 찾았다면 해당 위치에 블록을 핟당
        place(bp, asize);
        return bp;
    }

    // 찾지 못했다면 heap을 확장해야한다. (asize, CHUNKSIZE 중 큰 값 선택)
    extendsize = MAX(asize, CHUNKSIZE);

    // heap을 확장하고 새로운 가용 블록을 생성
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL; // 실패시 NULL
    
    // 새로 받은 블록을 할당
    place(bp, asize);

    return bp; // 할당된 bp 반환
}

/// @brief first-fit 함수 (가용 리스트에서 asize 이상인 첫 가용 블록을 탐색)
/// @param asize 할당하는 블록의 크기
/// @return 조건에 맞는 bp 반환, 실패 시 NULL 반환
static void *find_fit(size_t asize)
{
    void *bp;

    // 힙의 첫 블록부터 탐색
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        // 현재 블록이 가용 상태이고 크기가 요청 크기보다 크다면
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;

    // 찾지 못하면 NULL 반환
    return NULL;
}

/// @brief bp에 asize를 할당, 필요시 분할
/// @param bp  가용 블록의 bp 
/// @param asize 할당할 size 크기
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 가용 블록의 전체 크기

    // 16 byte 보다 (현재 - 요청크기) 보다 크다면
    if ((csize - asize) >= (2 * DSIZE))
    {
        // 요청한 크기 만큼의 블록을 할당
        PUT(HDRP(bp), PACK(asize, 1)); // header와 footer 에 asize, 1 갱신
        PUT(FTRP(bp), PACK(asize, 1));
        
        // 나머지 블록을 새로운 가용 블록으로 설정
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize - asize, 0)); // header 와 footer에 나머지 크기, 0 갱신 
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    // 남는 공간이 작다면 분할하지 않고 할당
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */

/// @brief 블록을 해체하고 인접한 가용 블록과 병합 시도하는 함수
/// @param bp 해제할 블록의 포인터
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // header에서 현재 블록 크기를 가지고옴

    PUT(HDRP(bp), PACK(size, 0)); // header / footer에 size, 0 가용 블록으로 갱신
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp); // 인접 블록이 있다면 병합
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