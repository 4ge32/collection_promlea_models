#ifdef TAGP
#ifdef LL_SC
#error "tag and ll_sc"
#endif
#endif

#define N 2
#define M N*3
#define NULL -1

typedef Mem {
    int data; // actual data
    int next; // next pointer
    int refc  // reference count for detecting double free
#ifdef TAGP
	byte tag; // type size is important
	         // int: no error on normal search depth
			 // byte: error on normal search depth
			 // bit: error on normal search depth, search have finished.
#endif
}

typedef Lfstack {
    int head; // head of lfstack, which is the mem array index.
#ifdef LL_SC
    int mon;
#endif
#ifdef TAGP
    byte tag; // ! it shall be as same as tag in Mem
#endif
}

Mem mem[M]; // index expresses memory address
Lfstack lfstack;
int pass = 0;

inline atomic_load(_cur) {
    d_step {
        _cur = lfstack.head;
		printf("%d: atomic_load -> %d\n", _pid, _cur);
#ifdef TAGP
        // tag pointer
        lfstack.tag = lfstack.tag + 1;
#endif
#ifdef LL_SC
        // actually, load shall only mark. Do not overwrite it.
        lfstack.mon = _pid;
#endif
    }
}

inline atomic_compare_and_exchange(_old, _new, _suc) {
    d_step {
#ifdef TAGP
		if
		:: mem[_old].tag != lfstack.tag ->
		   goto cas_end;
		:: else -> skip;
		fi;
#endif
        if
#ifndef LL_SC
        :: _old == lfstack.head ->
#else
        :: lfstack.mon == _pid->
#endif
           lfstack.head = _new;
#ifdef LL_SC
           lfstack.mon = -1;
#endif
           _suc = true;
		   printf("%d: CAS success -> %d->%d\n", _pid, _old, _new);
        :: else -> skip;
        fi;
#ifdef TAGP
cas_end:
#endif
    }
}

inline malloc(_addr) {
    d_step {
        do
        :: i < M ->
           if
           :: mem[i].refc == 0 ->
              mem[i].data = 0;
              mem[i].next = NULL;
              mem[i].refc = 1;
              _addr = i;
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
        assert(mem[_addr].refc == 1); // check double-free corruption
        mem[_addr].data = 0;
        mem[_addr].next = NULL;
        mem[_addr].refc = 0;
    }
}

proctype producer() {
    int addr;
    int orig;
    int next;
    int i = 0;
    bool suc = false;

    malloc(addr);
    mem[addr].data = _pid + 100;
produce_again:
    // lock-free push
    atomic_load(orig);
    mem[addr].next = orig;
    atomic_compare_and_exchange(orig, addr, suc);
    if
    :: suc == false ->
       goto produce_again;
    :: else -> skip;
    fi;

	// Finish
    pass = pass + 1;
}

proctype consumer() {
    int orig;
    int next;
    bool suc = false;

consume_again:
    // lock-free pop
    atomic_load(orig);
    if
    :: orig == NULL -> goto consume_again;
    :: else -> skip;
    fi;
    next = mem[orig].next;
    atomic_compare_and_exchange(orig, next, suc);
    if
    :: suc == true ->
       free(orig);
    :: else -> goto consume_again;
    fi;

	// Finish
    pass = pass + 1;
}

init {
#ifdef LL_SC
    printf("LL_SC\n");
#endif
#ifdef TAGP
    printf("TAGP\n");
#else
#ifndef LL_SC
    printf("CAS\n");
#endif
#endif

    // init
    lfstack.head = NULL;
    mem[0].data = 1;
    mem[0].next = 1;
    mem[0].refc = 1;
    mem[1].data = 2;
    mem[1].next = 2;
    mem[1].refc = 1;
    mem[2].data = 3;
    mem[2].next = 3;
    mem[2].refc = 1;
    mem[3].data = 4;
    mem[3].next = NULL;
    mem[3].refc = 1;
    mem[4].next = NULL;
    mem[5].next = NULL;
    lfstack.head = 0;
#ifdef TAGP
    lfstack.tag = 0;
#endif

    // should be as same as N*2
    run consumer();
    run consumer();
    run consumer();
    run producer();

    // wait until all processes finish
    d_step {
        pass == (N*2) -> skip;
    }

    int i = 0;
    printf("head: %d\n", lfstack.head);

    // validate model
    i = lfstack.head;
    int loop_cnt = 0;
    do
    :: i != NULL ->
       printf("mem[%d]: data=%d, next = %d, refc=%d\n",
              i, mem[i].data, mem[i].next, mem[i].refc);
       assert(mem[i].refc == 1);
       i = mem[i].next;
       loop_cnt = loop_cnt + 1;
    :: else -> break;
    od;
    assert(loop_cnt == 2);
}
