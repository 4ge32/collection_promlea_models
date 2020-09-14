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
