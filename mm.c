#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) // heap 늘리기 4kb

#define MAX(x,y) ((x)>(y) ? (x) : (y))

#define PACK(size, alloc) ( (size) | (alloc) ) // size = block size, alloc = 가용여부  => 합치면 주소

#define GET(p) (*(unsigned int*)(p)) // pointer p는 void형이라 참조불가하여 형변환
#define PUT(p, val) (*(unsigned int*)(p) = (int)(val)) // p에 주소담기 

#define GET_SIZE(p) (GET(p) & ~0x7) // 11111000 역순으로 비트연산시 000 앞값만 가져오겠다 (어차피 하위 3개 값은 항상 0임, 맨 끝은 0 1로 가용여부 표시)
#define GET_ALLOC(p) (GET(p) & 0x1) // 맨끝만 1 - 헤더에서 가용여부만 가져오겠다 

// compute address of header and footer
#define HDRP(bp) ((char*)(bp) - WSIZE)  // 시작주소에서 +4 = 헤더
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // bp주소 + block size - dsize = footer 앞

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 다음 블록 헤더로 이동
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 이전 블록 푸터로 이동
static char *heap_listp;
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *extend_heap(size_t words);


team_t team = {
    /* Team name */
    "jungle",
    /* First member's full name */
    "Seoin",
    /* First member's email address */
    "sower031@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};


int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1) {
        return -1;
    }

    PUT(heap_listp, 0); // padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue header 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // epilogue header
    heap_listp += (2*WSIZE); // prologue header 뒤 pointer 설정

    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) 
        return -1;
    return 0;
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 전블록 footer로 가서 가용여부 get
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 사이즈 확인

    if (prev_alloc && next_alloc) // case 1 둘다 할당되어 있을 때
        return bp;
    else if (prev_alloc && !next_alloc) { // case 2 이전 블록 할당, 다음 블록 가용
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록 헤더의 사이즈를 가져와서 현재 사이즈에 더해준다
        PUT(HDRP(bp), PACK(size, 0)); // 더 큰 크기로 헤더와 푸터 갱신
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) { // case 3 이전 블록 가용, 다음 블록 할당
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // prev block header 위치에 size 넣기
        bp = PREV_BLKP(bp); // 이전 블록 헤더로 이동시킴 ( 늘린 블록 헤더니까 )
    }
    else { // case 4 둘다 가용 블록
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 헤더 ~ 다음 푸터까지 넣어줘야함
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp; // 4 case 중 적용된 걸로 bp 리턴

}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 받은 워드를 8의 배수로 반올림한다 홀/짝수 판별 ? 홀수 : 짝수
    if ((long)(bp = mem_sbrk(size)) == -1) // bp를 사이즈만큼 늘린 뒤 long으로 반환하게 되면 bp는 블록 끝에 위치하게됨(-1)
        return NULL;
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // bp를 헤더에서 읽은 사이즈만큼 이동하고 앞으로 한칸 감. 즉 위치가 늘린 블록 끝에서 한 칸 간거라 거기가 epilogue header 위치임

    return coalesce(bp);
    
}


// 가용 리스트에서 블록 할당하는 함수
void *mm_malloc(size_t size) { 
    size_t asize; // 블록 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없다면 확장
    char *bp;

    if (size == 0) return NULL; // size 0이면 할당 X

    if (size <= DSIZE)
        asize = 2 * DSIZE; // 헤더 푸터 포함(8) + 최소 사이즈(8)
    else 
        asize = DSIZE * ( (size + (DSIZE) + (DSIZE - 1)) / DSIZE); //size > 8이라면 인접한 8의 배수로 만들어준다
    
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp; 
    }
    /* 위에서 안됐으면 fit 맞는 게 없다는 뜻이므로 메모리를 더 가져온다*/
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) 
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize) {
    void *bp;
    /* 초기값은 prologue header 뒤를 가리킨다 
    header의 사이즈가 0이 될 때까지 탐색한다 (first fit, 처음부터 끝까지 탐색) 그리고 epilogue header에 도달하면 값이 0이기 때문에 반복문을 종료한다.
    bp = 한 블록씩 이동
     */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 블록이 가용블록이고 내가 갖고있는 size를 담을 수 있다면
            return bp; // 바로 리턴
    }
    return NULL; // 종료되면 no return, no fit
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); // current block size
    if ((csize - asize) >= (2 * DSIZE)) { // 현재 블록 사이즈에 asize를 넣어도 최소 사이즈만큼 남는지 체크
        PUT(HDRP(bp), PACK(asize, 1)); // asize만큼 넣고 1로 상태변환
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); 
        PUT(HDRP(bp), PACK(csize - asize, 0)); // asize 넣고 남은 나머지 블록은 가용상태
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1)); // 조건 안맞아도 asize만 csize에 들어갈 수는 있으니까 csize에 다 할당함
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp)); // free해야하는 만큼 받아옴
    PUT(HDRP(bp), PACK(size, 0)); // 헤더랑 푸터 0으로 만들기
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp); // 가용 블록이 생기면 항상 연결시켜야함
}

void *mm_realloc(void *bp, size_t size)
{
    void *old_bp = bp;
    void *new_bp;
    size_t copySize;
    
    new_bp = mm_malloc(size);
    if (new_bp == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(old_bp));
    if (size < copySize)
      copySize = size;
    memcpy(new_bp, old_bp, copySize);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 copySize만큼의 문자를 new_bp로 복사해라)
    mm_free(old_bp);
    return new_bp;
}










