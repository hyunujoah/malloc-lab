#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "Enter the dragon",
    /* First member's full name */
    "D.T.",
    /* First member's email address */
    "dt@swjungle.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* 주소를 워드(4)로 정렬할지 더블 워드(8)로 정렬 할지 결정한다 */
#define ALIGNMENT 8 //ALIGNMENT 매크로를 8로 정의하면 8의 배수로 정렬하게되고, 4로 정의하면 4의 배수로 정렬하게 된다

/* 받은 주소가 워드의 배수가 되도록 만든다 */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) //8의 배수가 되게한다
//0x7은 000...0111을 나타낸다, ~인 NOT연산자를 적용하면 모든 비트가 반전되어 111...1000이 된다
//결론은 비트 단위 AND 연산자 &와 ~0x7을 사용하면 숫자를 8의 배수로 정렬할 수 있다
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본적인 상수와 매크로*/
#define WSIZE   4           //워드의 크기(바이트)
#define DSIZE   8           //더블워드의 크기(바이트)
#define CHUNKSIZE (1<<12)   //힙 영역을 한 번 늘릴 때 마다 늘려 줄 크기, (1<<12)는 2의 12승(4096)을 뜻한다, 이게 비트 마스크라고 한다
#define LISTLIMIT 20        //리스트의 최대 길이

#define MAX(x, y) ((x)>(y)?(x):(y))

/* 크기와 할당 상태를 1워드로 묶는다 */
#define PACK(size, alloc) ((size)|(alloc))

/* 주소 p에 있는 값을 읽고 쓴다 */
#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에서 블록의 크기와 할당상태를 읽어온다 */
#define GET_SIZE(p)     (GET(p)&~0x7)
#define GET_ALLOC(p)    (GET(p)&0x1)

/* 블록 포인터 bp를 받으면, 그 블록의 헤더와 풋터 주소를 반환한다 */
#define HDRP(bp) ((char *)(bp) - WSIZE) 
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* 블록 포인터 bp를 받으면, 그 이전 블록과 이후의 블록의 주소를 반환한다 */
#define SUCC_P_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PRED_P_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 블록 안에 저장된 리스트 이전 블록과 리스트 이후 블록의 주소를 가져온다. */
#define SUCC_P(bp)  (*(char **)(bp))
#define PRED_P(bp)  (*(char **)((bp)+WSIZE))

static void *heap_listp;                    //가상 메모리의 시작이 될 주소
static void *free_list[LISTLIMIT];          //가용 메모리의 리스트를 저장할 주소

static void *coalesce(void *bp);            //가용해진 블럭들을 합쳐주는 함수
static void *extend_heap(size_t words);     //가용 영역이 부족할 때 추가로 힙 영역을 요청하는 함수
static void *find_fit(size_t asize);        //메모리를 할당하기에 충분한 공간을 가진 블록을 찾는 함수
static void place(void *p, size_t size);    //메모리를 할당하고 남은 공간을 분리해주는 함수
static void list_add(void *p);              //가용 블록을 가용블록 리스트에 추가하는 함수
static void list_remove(void *p);           //가용 블록을 가용블록 리스트에서 제거해주는 함수

/* 
 * mm_init - 말록을 초기화
 */

int mm_init(void) { //메모리 관리자를 초기화하는 함수

    //리스트를 만든 곳에 쓰레기 값이 들어있지 않도록 초기화 해준다.
    for (int i = 0; i < LISTLIMIT; i++){
        free_list[i] = NULL;
    }

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //mem_sbrk는리눅스를 비롯한 여러 유닉스 계열 운영 체제에서도 지원
        //mem_sbrk 함수는 메모리 할당 및 해제를 위한 시스템 콜 중 하나이다
        //이함수는 운영체제에게 프로세스의 힙 공간을 동적으로 확장하거나 축소하도록 요청한다        
        return -1;
    PUT(heap_listp, 0); //heap_listp는 힙 메모리의 시작 주소를 나타내는 포인터 변수로 사용된다, 프롤로그 블록을 가리키는 포인터로 사용
    //heap_listp가 가리키는 주소에 0을 설정하여 프롤로그 블록의 첫번째 워드를 0으로 설정한다
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //heap_listp 포인터가 가리키는 위치에서 4바이트 떨어진 곳에
    //크기가 DSIZE(double word)이고 할당되어 있는 메모리 블록을 나타내는 풋터를 설정한다
    //이부분은 프롤로그 블록의 세번째 워드에 메모리 블록 풋터를 설정하는 것
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //PACK(DSIZE,1)에서 1은 할당되었음을 나타낸다
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); //여기서 크기가 0이라는 것은 해당 블록이 데이터를 저장하지 않고 힙영역의 끝을 표시한다는 의미
    

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) //가용 메모리가 부족할 경우 힙 영역을 추가로 확장한다, 이때, CHUNKSIZE만큼의 워드 크기를 확장한다
        return -1;
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size = (words%2) ? (words+1)*WSIZE : words*WSIZE; //words가 홀수인 경우, 즉 다음 짝수로 만들어준다
    //words가 짝수인 경우에는 words_WSIZE로 계산하여 확장할 크기를 결정한다
    if((long)(bp = mem_sbrk(size)) == -1) //mem_sbrk 함수를 호출하여 힙 메모리를 확장한다
    //만약 확장에 실패하면 -1을 반환하므로, 이를 체크하여 실패하면 NULL을 반환하고 함수를 종료한다
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    //주어진 포인터 bp의 헤더 주소를 의미한다
    PUT(FTRP(bp), PACK(size, 0));
    //주어진 포인터 bp의 푸터 주소를 의미한다
    PUT(HDRP(SUCC_P_BLKP(bp)), PACK(0,1));
    //SUCC_P는 주어진 포인터 bp 다음에 오는 블록의 주소를 나타낸다
    list_add(bp);
    //새로운 메모리 블록을 가용 메모리 리스트에 추가한다

    return coalesce(bp);
    //coalesce함수를 호출하여 가용 메모리 블록들이 파편화되지 않도록 합쳐준다
    //최종적으로 확장된 메모리 블록의 주소를 반환한다
}

/* 
 * mm_malloc - 메모리를 할당하고 필요하면 힙영역을 확장해달라고 요청한다
 */
void *mm_malloc(size_t size)
{
    size_t asize; //할당할 메모리 블록의 최종 크기를 저장하는 변수
    size_t extendsize; //필요에 따라 힙을 확장할 때 사용되는 크기를 저장하는 변수이다
    char *bp; //메모리 할당에 사용되는 포인터 변수이다

    if (size == 0) //만약 요청된 크기가 0이면 NULL을 반환하여 아무것도 할당하지 않는다
        return NULL;

    if (size<=DSIZE) //만약 요청된 크기가 DSIZE보다 작거나 같으면, 최소 블록 크기인 2*DSIZE를 할당한다
        asize = 2*DSIZE;
    else //그렇지 않으면, 요청된 크기에 대해 정렬을 수행하여 적절한 블록 크기를 계산한다
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE);

    if ((bp = find_fit(asize)) != NULL){ //메모리 할당을 위해 적합한 블록을 찾는다
        place(bp, asize); //적합한 블록을 찾았다면, 해당 블록에 메모리를 할당하고 해당 포인터를 반환한다
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE); //할당 요청된 크기인 asize와 미리 정의된 상수 CHUNKSIZE중 더 큰 값을 extendsize에 할당
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) 
        //extend_heap 함수는 요청된 크기의 메모리 블록을 힙 영역에 추가한다
        //extendsize/WSIZE는 확장할 메모리 크기를 워드 단위로 변환한 값이다
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize){ //가용 블록 리스트를 순회하면서 요청한 크기와 가장 근접한 크기를 가진 블록을 선택
    // Search for free block in segregated list
    size_t searchsize = asize;          //사이즈 값 변형을 위해 새로운 변수 선언, 검색할 블록의 크기를 asize로 설정한다
    char *ptr;                          //탐색을 위한 포인터
    int index = 0; //segregated list의 인덱스를 초기화한다
    while (index < LISTLIMIT) { //segregated list를 순회한다, LISTLIMIT는 리스트의 최대 길이를 나타낸다
        if ((index == LISTLIMIT - 1) || ((searchsize <= 1) && (free_list[index] != NULL))) {
            //현재 인덱스가 리스트의 마지막이거나, 검색 크기가 1이하이고 해당 인덱스에 가용 블록이 있는 경우,
            //즉, 원하는 크기 범위의 블록들이 들어있는 비어있지 않은 리스트인 경우에 이 조건을 만족한다
            ptr = free_list[index]; //해당 인덱스에 있는 가용 블록 리스트의 시작 포인터를 가져온다
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))))){ //리스트를 순회하면서 요청한 크기보다 큰 가용 블록을 찾는다
                ptr = SUCC_P(ptr); //ptr이 현재 가리키고 있는 블록의 다음 블록을 가리키는 포인터를 가져와서 ptr에 할당하는 코드
            }               //리스트가 비어있지 않지만, 사이즈가 작다면 리스트의 다음 원소로 이동한다
            if (ptr != NULL)
                return ptr;       //리스트 끝까지 확인했는데 맞는게 없는 것이 아니라면 값을 반환한다
        }
        searchsize >>= 1; //searchsize 변수의 값을 오른쪽으로 1비트씩 이동시키는 코드이다 
        //즉 2를 나눈 결과를 다시 searchsize에 할당하는 것
        index++;
    }
    return NULL;
}

/*
 * place - 가상 메모리 공간을 할당하고 크기에 따라 새로운 가용 블럭을 만든다.
 */
static void place(void *p, size_t size){
    size_t free_block = GET_SIZE(HDRP(p)); //p가 가리키는 메모리 블록의 크기를 읽어와서 free block에 저장한다
    list_remove(p); //할당된 메모리 블록을 리스트에서 제거한다, 이렇게 해서 해당 블록이 가용 메모리 리스트에 더 이상 포함되지않도록 한다
    if ((free_block-size)>=(2*DSIZE)){//(2*DSIZE)는 최소한의 가용 메모리 블록의 크기를 나타낸다
        PUT(HDRP(p), PACK(size, 1));//할당된 메모리 블록의 헤더를 업데이트하여 할당된 상태로 표시한다
        PUT(FTRP(p), PACK(size, 1));//할당된 메모리 블록의 푸터를 업데이트하여 할당된 상태로 표시한다
        p = SUCC_P_BLKP(p);
        //남은 가용 메모리 블록이 충분히 크다면, 해당 메모리 블록을 분할하여 남은 부분을 가용 메모리 리스트에 추가하기 위해
        //다음 메모리 블록으로 이동한다
        PUT(HDRP(p), PACK(free_block-size, 0));//분할된 가용 메모리 블록의 헤더를 업데이트하여 남은 가용 메모리 블록으로 표시한다
        PUT(FTRP(p), PACK(free_block-size, 0));//분하된 가용 메모리 블록의 풋터를 업데이트하여 남은 가용 메모리 블록으로 표시한다
        list_add(p);
    } else {//만약 남은 가용 메모리 블록이 요청된 크기보다 작다면, 해당 메모리 블록을 그대로 사용하고,
    //해당 메모리 블록을 할당된 상태로 표시하는 작업을 수행한다
    PUT(HDRP(p), PACK(free_block, 1));
    //메모리 블록의 헤더를 업데이트하여 해당 메모리 블록이 할당된 상태임을 표시한다, 이때, 할당된 상태의 헤더에는 블록의 크기만 표시힌다
    PUT(FTRP(p), PACK(free_block, 1));
    //메모리 블록의 풋터를 업데이트하여 해당 메모리 블록이 할당된 상태임을 표시한다, 이때, 풋터에도 할당된 상태의 풋터에는 블록의 크기만 표시한다
    }
}


//list_add - 가용블럭 리스트에 새로운 블럭의 정보를 넣는다.
//list_add 함수는 segregated list에 가용 블록을 삽입하는 역할을 한다 
static void list_add(void *p){
    size_t size = GET_SIZE(HDRP(p)); //변수를 사용하여 가용 블록의 크기를 저장한다
    int index = 0; //index 변수를 사용하여 가용 블록이 속할 segregated 리스트의 인덱스를 나타낸다
    void *insert_p = NULL; //변수는 가용 블록이 삽입될 위치를 나타내는 포인터이다

    //가용 블럭이 삽입될 인덱스를 검색한다.
    while ((index < LISTLIMIT - 1) && (size > 1)) { //리스트의 크기는 LISTLIMIT-1이다, LISTLIMIT은 20이다 
        size >>= 1; //size 변수의 값을 오른쪽으로 한 비트씩 이동한다, 즉, 2를 나눈값과 동일하다
        index++;
    }
    //리스트를 블럭의 크기별로 오름차순 시켜주기 위해 자리를 검색한다
    //삽입될 위치를 찾기 위해 리스트를 순회한다
    //search_p 포인터를 사용하여 리스트를 순회하며 적절한 위치를 찾는다
    void *search_p = free_list[index]; //free_list[index]는 해당 인덱스에 저장된 리스트의 첫 번째 노드를 가리킨다
    //search_p는 세그리게이트된 리스트의 특정 인덱스에 대한 포인터를 나타낸다
    //
    while ((search_p != NULL) && (size > GET_SIZE(HDRP(search_p)))) {
        //현재 노드 search_p가 NULL이 아닌 경우에만 반복한다, 이는 리스트의 끝에 도달할 때까지 반복을 계속한다는 의미
        //size>GET_SIZE(HDRP(search_p)):현재 노드의 블록 크기가 요청한 크기보다 작은 경우에만 반복한다
        //이는 리스트를 순회하면서 요청한 크기보다 큰 블록을 찾을 때까지 반복을 진행한다
        insert_p = search_p; //현재 노드를 insert_p에 저장한다
        search_p = SUCC_P(search_p); //현재 노드의 다음 노드를 현재 노드로 설정한다, 이를 통해 리스트를 순차적으로 탐색
    }
    //적절한 위치를 찾으면 주소를 저장해준다
    //적절한 위치를 찾은 후, 가용 블록을 해당 위치에 삽입한다, 만약 리스트가 비어있는 경우에는 가용 블록을 리스트의 처음으로 삽입한다
    
    if (search_p != NULL) { //적절한 위치를 찾은 경우이다
        if (insert_p != NULL) { //이전 노드가 있다면(insert_p가 NULL이 아닌 경우)
            SUCC_P(p) = PRED_P(search_p); //삽입할 블록의 다음 블록으로 이전 블록을 가리키게 한다
            PRED_P(search_p) = p; //다음 블록의 이전 블록으로 삽입할 블록을 가리키게 된다
            PRED_P(p) = insert_p; //삽입할 블록의 이전 블록으로 insert_p를 가리키게 한다
            SUCC_P(insert_p) = p; //이전 블록의 다음 블록으로 삽입할 블록을 설정한다
        } else { //이전 노드가 없는 경우, 즉, 삽입할 블록이 리스트의 맨 앞에 삽입되는 경우
            SUCC_P(p) = search_p; //삽입할 블록의 다음 블록으로 search_p를 가리키게 한다   
            PRED_P(search_p)= p; //search_p의 이전 블록으로 삽입할 블록을 가리키게 한다
            PRED_P(p) = NULL; //삽입할 블록의 이전 블록을 NULL로 설정한다
            free_list[index] = p; //리스트의 맨 앞에 있는 블록으로 삽입할 블록을 설정한다
        }
    } else {
        if (insert_p != NULL) {
            SUCC_P(p) =  NULL;
            PRED_P(p) = insert_p;
            SUCC_P(insert_p) = p;
        } else {
            SUCC_P(p) = NULL;
            PRED_P(p) = NULL;
            free_list[index] = p;
        }
    }
    return;
}

//list_remove - 가용블럭 리스트에서 블럭의 정보를 제거한다

static void list_remove(void *p){ //segregated free list에서 가용 블록을 제거하는 함수인 list_remove
    size_t size = GET_SIZE(HDRP(p));
    int index = 0; //size와 index를 초기화한다
    // Select segregated list
    while ((index < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        index++;
    }

    if (SUCC_P(p) != NULL) { //현재 블록의 다음 블록이 있는 경우
        if (PRED_P(p) != NULL) { //현재 블록의 다음 블록이 있는 경우
            PRED_P(SUCC_P(p)) = PRED_P(p); //다음 블록의 이전 블록을 현재 블록의 이전 블록으로 설정
            SUCC_P(PRED_P(p)) = SUCC_P(p); //이전 블록의 다음 블록을 현재 블록의 다음 블록으로 설정
        } else { //PRED_P(p)==NULL, 현재 블록의 이전 블록이 없는 경우
            PRED_P(SUCC_P(p)) = NULL; //다음 블록의 이전 블록 포인터를 NULL로 설정한다
            free_list[index] = SUCC_P(p); //세그리게이트된 리스트의 헤더를 SUCC_P(p)로 설정한다
            //free_list[index]는 해당 크기 범위의 가용 블록 리스트의 시작을 가리키는 포인터로서, 세그리게이트된 리스트의 헤더 역할을 한다
        }
    } else { //SUCC_P(p) == NULL, 현재 블록의 다음 블록이 없는 경우
        if (PRED_P(p) != NULL) { //현재 블록의 이전 블록이 있는 경우
            SUCC_P(PRED_P(p)) = NULL; //이전 블록의 다음 블록 포인터를 NULL로 설정한다
        } else { //현재 블록의 이전 블록도 없는 경우, 즉, 현재 블록이 리스트의 유일한 블록인 경우
            free_list[index] = NULL; //세그리게이트된 리스트의 헤더를 NULL로 설정한다
            //세그리게이트된 리스트의 헤더는 해당 세그리게이트된 리스트의 첫번째 블록을 가리키는 포인터이다
        } 
    }
    return;
}


//mm_free - 사용하지 않게 된 메모리를 반환한다.
void mm_free(void *ptr){
    size_t size = GET_SIZE(HDRP(ptr)); //메모리 블록의 크기를 가져온다, GET_SIZE 매크로는 주어진 포인터의 헤더에서 크기를 추출하는 역할을 한다
    PUT(HDRP(ptr), PACK(size, 0)); //메모리 블록의 헤더에 새로운 크기와 할당되지 않은 상태를 나타내는 비트를 설정한다
    PUT(FTRP(ptr), PACK(size, 0)); //메모리 블록의 풋터에도 동일한 크기와 할당되지 않은 상태를 나타내는 비트를 설정한다
    list_add(ptr);
    coalesce(ptr);
}


//coalesce - 가용블럭들이 파편화 되지 않도록 하나도 합쳐준다
//연속된 가용 블록들을 병합하여 메모리 단편화를 최소화하는 coalesce함수
static void *coalesce(void *bp){
    size_t PRED_P_alloc = GET_ALLOC(FTRP(PRED_P_BLKP(bp)));
    //PRED_P_BLKP(bp)는 현재 블록의 이전 블록의 주소를 가져온다
    //FTRP 매크로는 주어진 블록의 풋터 주소를 반환한다
    //따라서 FTRP(PRED_P_BLKP(bp))는 현재 블록의 이전 블록의 풋터 주소를 가져온다
    //GET_ALLOC 매크로는 저장된 할당 비트를 가져온다
    //GET_ALLOC(FTRP(PRED_P_BLKP(bp)))는 현재 블록의 이전 블록의 할당 여부를 나타내는 값을 가져온다
    size_t SUCC_P_alloc = GET_ALLOC(HDRP(SUCC_P_BLKP(bp)));
    //SUCC_P_BLKP(bp)는 현재 블록의 다음 블록의 주소를 가져온다
    //HDRP 매크로를 사용하여 해당 블록의 헤더 주소를 얻는다
    size_t size = GET_SIZE(HDRP(bp));
    //HDRP(bp)는 현재 블록의 헤더 주소를 가져온다
    //GET_SIZE 매크로는 주어진 블록의 크기를 가져온다
    //GET_SIZE(HDRP(bp))는 주어진 블록의 헤더에서 블록의 크기를 가져온다

    //기존의 블럭을 리스트에서 제거한다
    list_remove(bp);

    //조건에 따라 새로운 블럭을 생성한다
    if(PRED_P_alloc && !SUCC_P_alloc){ //현재 블록의 이전 블록은 할당되어 있고, 다음 블록은 비어 있는 경우
        list_remove(SUCC_P_BLKP(bp)); //다음 블록을 리스트에서 제거한다
        size += GET_SIZE(HDRP(SUCC_P_BLKP(bp)));
        //현재 블록의 크기에 GET_SIZE(HDRP(SUCC_P_BLKP(bp)))를 더해준다
        PUT(HDRP(bp), PACK(size, 0));
        //PACK(size,0)은 새로운 크기와 할당되지 않은 상태를 가진 헤더 값을 생성한다
        //PUT(HDRP(bp),PACK(size,0))는 bp가 가리키는 메모리의 헤더 위치(HDRP(bp))에 주어진 크기와 할당되지 않은 상태를 가진 값을 저장한다
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!PRED_P_alloc && SUCC_P_alloc){
        list_remove(PRED_P_BLKP(bp));
        size += GET_SIZE(HDRP(PRED_P_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PRED_P_BLKP(bp)), PACK(size, 0));
        bp = PRED_P_BLKP(bp);
    } else if (!PRED_P_alloc && !SUCC_P_alloc){
        list_remove(PRED_P_BLKP(bp));
        list_remove(SUCC_P_BLKP(bp));
        size += GET_SIZE(HDRP(PRED_P_BLKP(bp))) + GET_SIZE(FTRP(SUCC_P_BLKP(bp)));
        PUT(HDRP(PRED_P_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(SUCC_P_BLKP(bp)), PACK(size, 0));
        bp = PRED_P_BLKP(bp);
    }
    //새로운 블럭을 리스트에 넣는다.
    list_add(bp);
    return bp;
}

//mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 
void *mm_realloc(void *ptr, size_t size){
    void *oldptr = ptr;
    void *newptr;
    size_t copy_size;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copy_size = GET_SIZE(HDRP(oldptr));
    if (size < copy_size)
        copy_size = size;
    memcpy(newptr, oldptr, copy_size); //memcpy는 string.h를 써야된다
    mm_free(oldptr);
    return newptr;
}
