#define semaphore byte
semaphore sem = 1;
byte cnt = 0;

inline up() {
    sem = sem + 1
}

inline down() {
    d_step {
        sem > 0;
        sem = sem - 1
    }
}

active[3] proctype prc() {
    down();
    cnt++;
    assert(cnt == 1);
    cnt--;
    up();
}
