/* stack */
#define N 3

typedef Node {
    byte data;
    short next;
};

typedef Mem {
    Node node;
    byte refc;
}

Mem memory[N+1];
Node nodes[N+1];
byte mem_cnt = 0;
byte node_cnt = 1;
bool go = false;

inline malloc(node) {
    d_step {
        mem_cnt = mem_cnt + 1;
    };
}

inline free(node) {

}

inline cas(ncnt, old_top, new, ok) {
    d_step {
        if
        :: old_top.data == nodes[ncnt].data ->
           if
           ::old_top.next == nodes[ncnt].next ->
             assert(nodes[node_cnt].data == 0);
             nodes[node_cnt].data = new.data;
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
           old_top.data = nodes[node_cnt].data;
           old_top.next = nodes[node_cnt].next;
           local_stack_addr[_pid] = node_cnt;
       };
       new.next = local_stack_addr[_pid] - 1;
       /* compare and swap */
       cas(local_stack_addr[_pid], old_top, new, ok);
       if
       :: (ok == true) -> break;
       :: (ok == false) ->
          retry = retry + 1;
       fi;
    od;
    assert(ok == true);
}

byte seq = 0;
active[N] proctype producer() provided(go == true) {
    Node node;
    Node old_top;
    bool ok = false;
    byte retry = 0;
    node.data = _pid;
    node.next = -1;

    push(node, old_top, ok, retry)
    printf("pid=%d: stack[%d] == %d(%d) ok?=%d(%d)\n",
           _pid,
           _pid,
           nodes[_pid].data,
           nodes[_pid].next,
           ok, retry);

    /* Entire verification phase */
    d_step {
        seq = seq + 1;
        if
        :: seq == N ->
            int i = 0;
            int j = 0;
            do
            :: i < N ->
                printf("stack[%d]:%d(%d:%d)\n", i, nodes[i].data, nodes[i].next, retry);
                i = i + 1;
            :: else -> break;
            od;
            i = 0;
            /* Do you have duplicated nodes? */
            do
            :: i < N - 1 ->
               j = i + 1;
               do
               :: j < N ->
                  assert(nodes[i].data != nodes[j].data);
                  printf("(i, j) = (%d, %d)\n", i, j);
                  j = j + 1;
               :: else -> break;
               od;
               i = i + 1;
            :: else -> break;
            od;
            /* Do you have dataid pointers? */
            i = 0;
            do
            :: i < N - 1 ->
               j = i + 1;
               do
               :: j < N ->
                  if
                  :: nodes[i].data > 0 ->
                     assert(nodes[i].next == i-1);
                  fi;
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
           old_top.data = nodes[node_cnt].data;
           old_top.next = nodes[node_cnt].next;
           local_stack_addr[_pid] = node_cnt;
       }
       if
       :: node_cnt == 0 -> break;
       fi;
       if
       :: nodes[local_stack_addr[_pid] - 1].data == 0 ->
          break;
       :: else -> skip;
       fi;
       /* compare and swap */
       cas(local_stack_addr[_pid], old_top, node, ok)
       if
       :: (ok == true) ->
          success = true;
          break;
       :: else -> printf("H\n"); break;
       fi;
    od;
}

active proctype consumer() provided(go == true) {
    Node node;
    node.data = 0;
    node.next = -1;
    Node old;
    bool ok = false;
    pop(node, old, ok);
}


init {
    int init_cnt = 0;
    do
    :: init_cnt < N ->
        nodes[init_cnt].data = 0;
        nodes[init_cnt].next = -1;
        init_cnt = init_cnt + 1;
    :: else -> break
    od;
    go = true;
}