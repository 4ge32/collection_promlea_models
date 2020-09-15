#define N 2

typedef Mem {
    byte data; // actual data
    byte mon;  // monitor the access of the memory
    int lcnt;  // emulate C pointer
}

Mem lfstack[N+2];
Mem lfs_cnt;
bool go = false;
int pass = 0;


inline end() {
    d_step {
        pass = pass + 1;
        if
        :: pass == N*2 ->
           int i = 0;
           do
           :: i < N ->
              assert(lfstack[i].data == i);
              printf("lfstack[%d]: %d\n",
                     i, lfstack[i].data);
              i = i + 1;
           :: else -> break;
           od;
        :: else -> skip
        fi;
    }
}

inline load(ptr) {
#ifndef LL_SC
    d_step {
        ptr = lfs_cnt.lcnt;
    }
#else
    d_step {
        ptr = lfs_cnt.lcnt;
        lfs_cnt.mon = _pid;
    }
#endif
}

inline cas(old, new, suc) {
#ifndef LL_SC
    //d_step {
        if
        :: lfs_cnt.lcnt == old ->
           lfs_cnt.lcnt = new;
           suc = true;
        :: else ->
           suc = false;
        fi;
    //}
#else
    //d_step {
        if
        :: lfs_cnt.mon == _pid ->
           lfs_cnt.lcnt = new;
           suc = true;
        :: else ->
           suc = false;
        fi;
    //}
#endif
}

active[N] proctype producer() provided (go == true) {
    Mem m;
    int old;
    int new;
    bool suc = false;

produce:
    load(old);
    new = old + 1;
    d_step {
    cas(old, new, suc);
    if
    :: suc == true ->
       lfstack[new].data = _pid + 100;
       printf("pid=%d: lfstack[%d]=%d\n",
               _pid, new, _pid + 100);
    :: else -> skip;
    fi;
    }
    if
    :: suc == false -> goto produce;
    :: else -> skip;
    fi;

    end();
}

active[N] proctype consumer() provided(go == true) {
    Mem m;
    int old;
    int new;
    bool suc = false;

consume:
    load(old);
    if
    :: old < 0 ->
       goto consume;
    :: else -> skip
    fi;
    new = old - 1;
    d_step {
    cas(old, new, suc);
    if
    :: suc == true ->
       lfstack[old].data = old;
       printf("pid=%d: lfstack[%d]=%d\n",
               _pid, old, old);
    :: else -> skip;
    fi;
    }
    if
    :: suc == false -> goto consume;
    :: else -> skip;
    fi;

    end();
}

init {
    lfs_cnt.lcnt = -1;
    go = true;
}
