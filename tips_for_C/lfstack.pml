#define N 3

typedef Node {
    byte data;
    short next;
};

typedef Mem {
    Node node; // the actual object
    byte refc; // to detect double free corruption
    byte mon;  // monitor the access of the memory
}

Node nodes[N+2];

/* Index = memory address */
Mem mem[N+2];
Mem lfstack[N+2];

int lfs_cnt = 1;

// If return node.addr = 0,
// It means ENOMEM.
inline malloc(node) {
    d_step {
        byte lc = 1;
        do
        :: lc <= N + 1 ->
           if
           :: mem[lc].refc == 0 ->
              node.refc = 1;
              break
           fi;
           lc = lc + 1
        :: else -> break
        od
    }
}

inline free(node) {
    d_step {
        assert(node.refc == 1);
        assert(node.addr != 0);
        mem[node.addr].refc = 0;
    }
}

inline load(org) {
#ifndef ARM
    d_step {
        org.node.data = lfstack[lfs_cnt].node.data;
        org.node.next = lfs_cnt - 1;
        printf("[LOAD] pid=%d---\n", _pid);
    }
#else
    d_step {
        org.node.data = lfstack[lfs_cnt].node.data;
        org.node.next = lfs_cnt - 1;
        lfstack[lfs_cnt].mon = _pid + 100;
        printf("[RESERVED] lfstack[%d].mon = %d\n", lfs_cnt, _pid);
    }
#endif
}

/* Simulate comparen and swap at C11 */
inline cas(expected, desired, suc) {
#ifndef ARM
    d_step {
        if
        :: lfstack[lfs_cnt].node.data == expected.node.data ->
           if
           :: lfstack[lfs_cnt].node.next == 0 ->
              lfstack[lfs_cnt].node.data = desired.node.data;
              lfstack[lfs_cnt].node.next = desired.node.next;
              lfs_cnt = lfs_cnt + 1;
              suc = true;
           :: else ->
              expected.node.data = lfstack[lfs_cnt].node.data;
              expected.node.next = lfstack[lfs_cnt].node.next;
              suc = false;
           fi;
        :: else ->
           expected.node.data = lfstack[lfs_cnt].node.data;
           expected.node.next = lfstack[lfs_cnt].node.next;
           suc = false;
        fi
    }
#else
    d_step {
        if
        :: lfstack[lfs_cnt].mon == _pid + 100 ->
           lfstack[lfs_cnt].node.data = desired.node.data;
           lfstack[lfs_cnt].node.next = desired.node.next;
           lfs_cnt = lfs_cnt + 1;
           lfstack[lfs_cnt].mon = 0;
           suc = true;
        :: else ->
           expected.node.data = lfstack[lfs_cnt].node.data;
           expected.node.next = lfstack[lfs_cnt].node.next;
           lfstack[lfs_cnt].mon = 0;
           suc = false;
        fi
    }
#endif
}

bool go = false;
int pass = 0;
active[N] proctype producer() provided (go == true) {
    Mem m;
    Mem org
    byte top;
    bool suc = false;
    malloc(m);
    m.node.data = _pid + 100;

cas_again:
    load(org);
    m.node.next = org.node.next;
    printf("[CAS]%d: data=%d, next=%d\n",
          _pid,
          m.node.data,
          m.node.next);
    cas(org, m, suc);
    if
    :: suc == false -> printf("[FAIL]%d: fail\n", _pid); goto cas_again
    :: else -> skip
    fi;
    printf("[SUCCESS]pid=%d: Success\n", _pid);

    /* Validate the result */
    atomic {
    pass = pass + 1;

    int ccc = 0;
    if
    :: pass == N ->
        do
        :: ccc < N+1 ->
           printf("lfstack[%d]: data(%d) next(%d)\n",
                  ccc,
                  lfstack[ccc].node.data,
                  lfstack[ccc].node.next);
           if
           :: ccc >= 1 ->
              //assert(lfstack[ccc].node.next == ccc - 1);
              skip
           :: else -> skip;
           fi;
           ccc = ccc + 1;
        :: else -> break;
        od
        printf("Top: %d\n", lfs_cnt-1);
    :: else -> skip;
    fi;
    }
}

proctype consumer() {
    //lfs_cnt = lfs_cnt - 1;
    skip
}

init {
    int st = 1;
    do
    :: st < N+1 ->
       lfstack[st].node.next = st;
       st = st + 1;
    :: else -> break
    od;
    st = 0;
    do
    :: st < N+2 ->
       lfstack[st].refc = 0;
       lfstack[st].mon = 0;
       lfstack[st].node.data = 100;
       lfstack[st].node.next = 0;
       printf("lfstack[%d]: %d\n", st, lfstack[st].node.next);
       st = st + 1;
    :: else -> break
    od;
    go = true;
    //run consumer();
}
