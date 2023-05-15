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
    "8조",
    /* First member's full name */
    "Sangju Kim",
    /* First member's email address */
    "rlatkdwn3379@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};
// 기본 상수 및 매크로
#define WSIZE 8             // 워드 사이즈 8바이트
#define DSIZE 16            // 더블 워드는 16 바이트
#define CHUNKSIZE (1 << 12) // heap늘릴땐 4kb만큼
// 단어의 크기 및 할당된 비트채우기
#define MAX(x, y) ((x) > (y) ? (x) : (y)) // x>y가 참이면 x 반환 거짓이면 y

#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값 리턴

// 주소 p 에서 읽고 쓰기
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
// 주소 p 에서 크기 및 할당된 필드 읽기
#define GET_SIZE(p) (GET(p) & ~0x7) // 뒤에 3비트를 제외하고 읽어옴
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 가용 확인

// 지정된 블록의 header와 footer 의 주소 계산
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 지정된 블록의 다음 블록과 이전 블록의 주소 계산 주소
#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE)))

/* single word (4) or double word (8) alignment 아까 지운거*/
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *extend_heap(size_t words);    // 새 가용 블록으로 힙 확장
static void *coalesce(void *bp);           // 인접 가용 블록들과 통합
static void *find_fit(size_t asize);       // 가용 리스트를 처음부터 검색해서 크기가 맞는 첫 번째 가용 블록을 선택
static void place(void *bp, size_t asize); // 가용 공간과 할당할 사이즈가 들어갈 수 있는 공간에 header와 footer에
                                           // 정보를 넣어주고 공간 할당을 하고 남은 부분이 있으면
                                           // (넣어줄 가용 블록 크기 - 할당할 크기) 만큼을 가용공간으로 만듬
static void *heap_listp;
static void *next_fit;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 초기에 비어있는 힙 생성하기
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    PUT(heap_listp, 0);                            // 패딩 생성
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 끝점 기록 0,1
    heap_listp += (2 * WSIZE);                     // heap_listp 포인터를 prologue header와 footer 사이에 위치 시킨다.
    next_fit = heap_listp;
    // 청크사이즈 바이트의 사용 가능한 블록으로 확장
    // 공간이 없으면 -1
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 짝수 단어 할당으로 정렬 유지하기!
    // 짝수 * 4는 무조건 8의 배수이기 때문에 홀수일 때 짝수로 만들어서 *4를 함
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 홀수면 (words+1) * WSIZE 반환 짝수면 words * WSIZE 반환
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    // 가용가능한 블록의 header와 footer 그리고 epilogue header 초기화
    PUT(HDRP(bp), PACK(size, 0));         // header 초기화
    PUT(FTRP(bp), PACK(size, 0));         // footer 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // footer뒤에 epilogue 위치 설정

    // 새 가용 블록으로 힙을 확장하고 이전 블록이 가용 가능하다면 병합한다
    return coalesce(bp);
}

// mm_malloc - brk 포인터를 증가시켜 블록을 할당하는 함수
// 항상 size가 다중배열인 블록을 할당한다?
void *mm_malloc(size_t size)
{
    size_t asize;      // 블록 사이즈
    size_t extendsize; // 맞는 fit이 없을때 확장 크기
    char *bp;

    // size 0 일때 무시
    if (size == 0)
    {
        return NULL;
    }
    // overhead나 정렬 요청에 블록의 크기조정
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        /* 할당할 크기가 8바이트보다 작으면 asize에 16바이트를 담음
       할당할 크기가 8바이트보다 크면 8의 배수로 맞춰줘야되기 때문에
       (header/footer의 크기 8바이트 + 7바이트 + 할당할 크기) / 8을 하면
       나머지는 버려지고 몫만 남는데 그 몫 * 8을 하면 할당할 크기를 담을 수 있는
       최소한의 크기의 8의 배수를 구할 수 있음 */
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }
    // fit 맞는 가용 가능한 리스트 찾기
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp; // place된 블록 반환
    }
    // 적합한걸 못찾았으면 더 많은 메모리를 할당받고 블록을 배치한다.
    extendsize = MAX(asize, CHUNKSIZE);
    // 확장 불가면 NULL 반환
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    // 확장가능하면 asize 만큼 늘리고 재배치
    place(bp, asize);
    return bp;
}

// static void *find_fit(size_t asize)
// {
//     /* First-fit search */
//     void *bp;

//     // GET_SIZE(HDRP(bp)) > 0 : 블록의 크기가 0 보다 작을 때, 즉 apilogue를 만날 때까지 반복
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         // 현재 블록이 가용 상태이고, 할당하고 싶은 사이즈(asize)가 현재 블록보다 작을때 bp 반환
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
//         {
//             return bp;
//         }
//     }
//     // for문이 종료됬다면, 알맞는 크기가 없으니 NULL 반환
//     return NULL;
// }

static void *find_fit(size_t asize)
{
    /* NEXT-fit search */
    void *bp;

    // GET_SIZE(HDRP(bp)) > 0 : 블록의 크기가 0 보다 작을 때, 즉 epilogue를 만날 때까지 반복
    for (bp = next_fit; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        // 현재 블록이 가용 상태이고, 할당하고 싶은 사이즈(asize)가 현재 블록보다 작을때 bp 반환
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            next_fit = bp;
            return bp;
        }
    }
    // for (bp = heap_listp; bp < next_fit; bp = NEXT_BLKP(bp))
    // {
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
    //     {
    //         next_fit = bp;
    //         return bp;
    //     }
    // }
    // for문이 종료됬다면, 알맞는 크기가 없으니 NULL 반환
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

    if ((csize - asize) >= (2 * DSIZE))
    {                                  // 분할 후에 이 블록의 나머지가 최소 블록 크기(16 bytes)와 같거나 크다면
        PUT(HDRP(bp), PACK(asize, 1)); // header 위치에 asize 만큼 넣고 할당 상태로 변경
        PUT(FTRP(bp), PACK(asize, 1)); // footer 위치에 asize 만큼 넣고 할당 상태로 변경
        bp = NEXT_BLKP(bp);            // bp 위치를 다음 블록 위치로 갱신
        // asize 할당 후 남은 공간 분할 후 가용 상태로 변경
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        // 아니라면, 그냥 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
// 사용하지않는 블록 해제
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 여부 체크
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 여부 체크
    size_t size = GET_SIZE(HDRP(bp));                   // 현재블록 헤더의 사이즈 확인

    if (prev_alloc && next_alloc)
    {                  // case 1:  현재 블록의 이전 블록, 다음 블록 모두 할당된 상태
        next_fit = bp; // next_fit에 bp위치를 저장
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {                                          // case 2: 현재 블록의 이전 블록은 할당된 상태, 다음 블록은 가용상태
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록에 다음 블록 사이즈 더해줌
        PUT(HDRP(bp), PACK(size, 0));          // 현재블록 header에 size 넣고 가용으로 변경
        PUT(FTRP(bp), PACK(size, 0));          // 다음 블록 footer에 size넣고 가용으로 변경
    }
    else if (!prev_alloc && next_alloc)
    {                                            // case 3: 현재블록의 이전 블록은 가용 & 다음 블록은 할당
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 현재 블록에 이전 블록 사이즈 더해줌
        PUT(FTRP(bp), PACK(size, 0));            // 현재블록 footer에 사이즈 넣고 가용으로 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 header에 사이즈 넣고 가용으로 변경
        bp = PREV_BLKP(bp);                      // bp를 이전 블록 payload 시작 위치로 변경
    }
    // case 4: 현재 블록의 이전 다음 블록 전부 가용 상태
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // size에 이전, 다음 블록의 사이즈를 더해준다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                               // 이전 블록 header에 size를 넣고 가용상태로 변경
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                               // 다음 블록 footer에 size를 넣고 가용상태로 변경
        bp = PREV_BLKP(bp);                                                    // bp를 이전 블록 payload 시작 위치로 변경
    }
    next_fit = bp;
    return bp;
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
    // copySize = GET_SIZE(HDRP(oldptr));
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    // newptr : 복사받을 메모리를 가리키는 포인터, oldptr : 복사할 메모리를 가리키는 포인터, copySize : 크기
    memcpy(newptr, oldptr, copySize); // 메모리 복사 함수 memcpy
    // 기존의 메모리 free
    mm_free(oldptr);
    return newptr;
}