#define NUM_CORE 2
#define NUM_THREAD 2

/** Thread control block */
typedef tcb_t {
    byte tid;
}

typedef core_t {
    tcb_t tcb[NUM_THREAD];
}

core_t core[NUM_CORE];

init {
    printf("Hello, World\n");
}