#define N 5

mtype = {THINKING, HUNGRY, EATING};
bit fork[N] = {0};
bit state[N] = {THINKING};

#define semaphore byte
semaphore sem = 1;
byte count = 0;

inline up() {
    sem = sem + 1
}

inline down() {
    d_step {
        sem > 0;
        sem = sem - 1
    }
}

active proctype another() {
  do
  :: true ->
  progress:
     state[_pid] = HUNGRY;
     down();
     atomic { fork[_pid] == 0 -> fork[_pid] = 1 };
     atomic { fork[(_pid+1)%N] == 0 -> fork[(_pid+1)%N] = 1 };
     state[_pid] = EATING;
     atomic { fork[(_pid+1)%N] = 0; fork[_pid] = 0 }
     state[_pid] = THINKING;
     up();
  od
}

active[N-1] proctype philosopher() {
  do
  :: true ->
     state[_pid] = HUNGRY;
     down();
     atomic { fork[_pid] == 0 -> fork[_pid] = 1 };
     atomic { fork[(_pid+1)%N] == 0 -> fork[(_pid+1)%N] = 1 };
     state[_pid] = EATING;
     atomic { fork[(_pid+1)%N] = 0; fork[_pid] = 0 }
     state[_pid] = THINKING;
     up();
  od
}
