mtype = {msg, ack};
chan line = [1] of {mtype, byte};

active proctype Sender () {
    byte b = 0;
    byte c;
    do
    :: line!msg(b);
        if
        :: b < 5 -> b++
        :: else -> b = 0
        fi;
        line?ack(c);
        c == b
    od
}

active proctype Receiver() {
    byte c = 0;
    byte b;
    do
    :: line?msg(b);
        b == c
        if
        :: c < 5 -> c++
        :: else -> c = 0
        fi;
        line!ack(c);
    od;
}
