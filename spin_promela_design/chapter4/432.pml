byte cnt = 0;
mtype = {LOCKED, UNLOCKED};
byte mutex = UNLOCKED;

inline lock() {
    d_step {
        mutex == UNLOCKED;
        mutex = LOCKED
    }
}

inline unlock() {
    mutex = UNLOCKED
}

active[2] proctype count10() {
again:
    lock();
    if
    :: cnt  < 10 ->
       cnt++;
    :: else
    fi;
    unlock();
    if
    :: cnt == 10 -> goto ten;
    :: else -> goto again;
    fi;

ten:
    assert(cnt == 10)
}