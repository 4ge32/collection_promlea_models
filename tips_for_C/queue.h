int int_mem[9];
int int_valid[9];
typedef node_t {
    int next;
    int val;
}
node_t node_t_mem[9];
int node_t_valid[9];
typedef queue_t {
    int head;
    int tail;
    int h_lock;
    int t_lock;
}
queue_t queue_t_mem[9];
int queue_t_valid[9];

proctype initialize(chan in_init; int Q) {
    int node_t_ct;
    int dummy;
    int tmp;
    atomic {
        node_t_ct = 1;
        do
        :: (node_t_ct >= 9) -> break
        :: else ->
           if
           :: (node_t_valid[node_t_ct] == 0) ->
              node_t_valid[node_t_ct] = 1;
              break
           :: else -> node_t_ct++
           fi
        od;
        assert(node_t_ct < 9);
        tmp = node_t_ct;
        node_t_ct = 1
    };
    dummy = tmp;
    node_t_mem[dummy].next = 0;
    node_t_mem[dummy].val = 0;
    queue_t_mem[Q].tail = dummy;
    queue_t_mem[Q].head = queue_t_mem[Q].tail;
    queue_t_mem[Q].t_lock = 0;
    queue_t_mem[Q].h_lock = queue_t_mem[Q].t_lock;
    //in_init ! 0;
    goto end;
end:
    printf("End of initialize")
}

proctype enqueu(chan in_enq; int Q; int val) {
    skip
}

proctype dequeue(chan in_deq) {
    skip
}
