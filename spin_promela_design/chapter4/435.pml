mtype = {BLUE, RED, YELLOW, LOCKED, UNLOCKED};
mtype mutex1 = LOCKED;
mtype mutex2 = LOCKED;
mtype state1 = BLUE;
mtype state2 = RED;

inline lock(m) {
    d_step {
        m == UNLOCKED ->
        m = LOCKED
    }
}

inline unlock(m) {
    m = UNLOCKED
}

active proctype signal1() {
    do
    :: state1 = RED;
       unlock(mutex2);
       lock(mutex1);
       state1 = BLUE
    od
}

active proctype signal2() {
    do
    :: lock(mutex2);
       state2 = BLUE;
       state2 = RED;
       unlock(mutex1)
    od
}

never {
    BLUE_RED:
    if
    :: state1 == BLUE && state2 == RED -> goto BLUE_RED
    :: state1 == RED  && state2 == RED  -> goto RED_RED
    :: else -> goto accept
    fi;
}