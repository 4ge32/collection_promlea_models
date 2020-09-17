#define LL_SC
#define N 2
#define M N*3
#define NULL -1

typedef Mem {
    int data; // actual data
    int next; // next pointer
    int refc  // reference count for detecting double free
    int mon;  // monitor the access of the memory
}

typedef Lfstack {
    int head;
    int mon;
}

Mem mem[M]; // index expresses memory address
Lfstack lfstack;
int pass = 0;

inline atomic_load(_cur) {
    d_step {
        _cur = lfstack.head;
#ifdef LL_SC
        // actually, load shall only mark. Do not overwrite it.
        lfstack.mon = _pid;
#endif
    }
}

inline compare_and_swap(_new) {
    d_step {
        if
#ifndef LL_SC
        :: orig == lfstack.head ->
#else
        :: lfstack.mon == _pid->
#endif
	   assert(_new != -1);
           lfstack.head = _new;
       	   printf("%d: lfs=%d\n", _pid, lfstack.head);
#ifdef LL_SC
           lfstack.mon = -1;
#endif
           suc = true;
        :: else -> skip;
        fi;
    }
}

inline push() {
    atomic_load(orig);
    mem[addr].next = orig;
    printf("%d: addr=%d, next=%d\n", _pid, addr, mem[addr].next)

    compare_and_swap(addr);
}

inline pop() {
    atomic_load(orig);
    if
    :: orig == NULL -> goto end;
    :: else -> skip;
    fi;
    next = mem[orig].next;

    compare_and_swap(next);
end:
    skip
}

inline malloc() {
    d_step {
        do
        :: i < M ->
           if
           :: mem[i].refc == 0 ->
              mem[i].data = 0;
              mem[i].next = NULL;
              mem[i].refc = 1;
              mem[i].mon = 0;
              addr = i;
              break;
           :: else -> skip;
           fi;
           i = i + 1;
        :: else -> break;
        od;
    }
}

inline free(_addr) {
    d_step {
        assert(mem[_addr].refc == 1);
        mem[_addr].data = 0;
        mem[_addr].next = NULL;
        mem[_addr].refc = 0;
        mem[_addr].mon = -1;
    }
}

proctype producer() {
    int addr;
    int orig;
    int next;
    int i = 0;
    bool suc = false;

    malloc();
produce_again:
    mem[addr].data = _pid + 100;
    push();
    if
    :: suc == false ->
       goto produce_again;
    :: else -> skip;
    fi;
   printf("%d: mem[%d].next=%d, lfs=%d\n", _pid, addr, mem[addr].next, lfstack.head);

    pass = pass + 1;
}

proctype consumer() {
    int orig;
    int next;
    bool suc = false;

consume_again:
    pop();
    if
    :: suc == true ->
       free(orig);
    :: else -> goto consume_again;
    fi;

    pass = pass + 1;
}

init {
#ifdef LL_SC
    printf("LL_SC\n");
#else
    printf("CAS\n");
#endif
    lfstack.head = NULL;

    // init
    mem[0].data = 1;
    mem[0].next = 1;
    mem[0].refc = 1;
    mem[0].mon = -1;
    mem[1].data = 2;
    mem[1].next = 2;
    mem[1].refc = 1;
    mem[1].mon = -1;
    mem[2].data = 3;
    mem[2].next = 3;
    mem[2].refc = 1;
    mem[2].mon = -1;
    mem[3].data = 4;
    mem[3].next = NULL;
    mem[3].refc = 1;
    mem[3].mon = -1;
    mem[4].next = NULL;
    mem[4].mon = -1;
    mem[5].next = NULL;
    mem[5].mon = -1;

    lfstack.head = 0;
    lfstack.mon = -1;

    run consumer();
    run consumer();
    run consumer();
    run producer();

    // wait until all processes finish
    d_step {
        pass == 4 -> skip;
    }

    int i = 0;
    printf("head: %d\n", lfstack.head);
    //do
    //:: i < M ->
    //   printf("mem[%d]: data=%d, next = %d, refc=%d\n",
    //          i, mem[i].data, mem[i].next, mem[i].refc);
    //   i = i + 1;
    //:: else -> break;
    //od;
    i = lfstack.head;
    int loop_cnt = 0;
    do
    :: i != NULL ->
       printf("mem[%d]: data=%d, next = %d, refc=%d\n",
              i, mem[i].data, mem[i].next, mem[i].refc);
       //assert(mem[i].refc == 1);
       i = mem[i].next;
       loop_cnt = loop_cnt + 1;
    :: else -> break;
    od;
    assert(loop_cnt == 2);
}
