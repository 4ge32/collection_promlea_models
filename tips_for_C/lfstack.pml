/* stack */
#define N 3

typedef Node {
    byte val;
    short next;
};

Node nodes[N+1];
byte node_cnt = 1;

inline do_cas(ncnt, old_top, new, ok) {
    d_step {
        if
        :: old_top.val == nodes[ncnt].val ->
           if
           ::old_top.next == nodes[ncnt].next ->
             assert(nodes[node_cnt].val == 0);
             nodes[node_cnt].val = new.val;
             nodes[node_cnt].next = new.next;
             node_cnt = node_cnt + 1;
             ok = true
           :: else -> ok = false
           fi
        :: else ->
           ok = false
        fi
    }
}

inline push(new, old_top, ok, retry) {
    byte local_stack_addr[N]; /* memory address */
    do
    :: true ->
       /* atomic_load() */
       d_step {
           old_top.val = nodes[node_cnt].val;
           old_top.next = nodes[node_cnt].next;
           local_stack_addr[_pid] = node_cnt;
       };
       new.next = local_stack_addr[_pid] - 1;
       /* compare and swap */
       do_cas(local_stack_addr[_pid], old_top, new, ok);
       if
       :: (ok == true) -> break;
       :: (ok == false) ->
          retry = retry + 1;
       fi;
    od;
    assert(ok == true);
}

byte seq = 0;
active[N] proctype producer() {
    Node node;
    Node old_top;
    bool ok = false;
    byte retry = 0;
    node.val = _pid + 1;
    node.next = -1;

    push(node, old_top, ok, retry)
    printf("pid=%d: stack[%d] == %d(%d) ok?=%d(%d)\n",
           _pid,
           _pid,
           nodes[_pid].val,
           nodes[_pid].next,
           ok, retry);

    /* Entire verification phase */
    d_step {
        assert(nodes[seq].val > 0);
        seq = seq + 1;
        if
        :: seq == N ->
            int i = 0;
            do
            :: i < N ->
                printf("stack[%d]:%d(%d:%d)\n", i, nodes[i].val, nodes[i].next, retry);
                //assert(nodes[i].next == i);
                i = i + 1;
            :: else -> break;
            od;
            i = 0;
            do
            :: i < N - 1 ->
               int j = i + 1;
               do
               :: j < N ->
                  //assert(nodes[i].val != nodes[j].val);
                  //printf("(i, j) = (%d, %d)\n", i, j);
                  j = j + 1;
               :: else -> break;
               od;
               i = i + 1;
            :: else -> break;
            od;
        :: else -> skip
        fi
    }
}

inline pop(node, old_top, ok) {
    byte local_stack_addr[N * 2];
    bool success = false;
    do
    :: true ->
       /* atomic_load() */
       d_step {
           old_top.val = nodes[node_cnt].val;
           old_top.next = nodes[node_cnt].next;
           local_stack_addr[_pid] = node_cnt;
       }
       if
       :: node_cnt == 0 -> break;
       fi;
       if
       :: nodes[local_stack_addr[_pid] - 1].val == 0 ->
          break;
       :: else -> skip;
       fi;
       /* compare and swap */
       do_cas(local_stack_addr[_pid], old_top, node, ok)
       if
       :: (ok == true) ->
          success = true;
          break;
       :: else -> printf("H\n"); break;
       fi;
    od;
}

active proctype consumer() {
    Node node;
    node.val = 0;
    node.next = 0;
    Node old;
    bool ok = false;
    pop(node, old, ok);
}

//initialize