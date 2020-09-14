/* stack */
#define N 3

typedef Node {
    byte data;
    short next;
};

typedef Mem {
    Node node; // the actual object
    byte refc; // to detect double free corruption
    byte addr; // to express the object address
}

Mem memory[N+1];
Node nodes[N+1];

// If return node.addr = 0,
// It means ENOMEM.
inline malloc(node) {
    d_step {
        node.addr = 0;
        byte lc = 1;
        do
        :: lc < N+1 ->
           if memory[lc].refc == 0 ->
              node = memory[lc];
              node.refc = 1;
              node.addr = lc;
              break
           fi;
           lc += 1;
        :: else -> break
        od
    };
}