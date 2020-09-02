//#include "../tips_for_C/queue.h"

#define N 2

// The mfutex api behavior emulation from
// the view of api-user level.
bit sleeper[N*2] = {false}
inline mcos_mfutex_wake() {
    byte w = 0
    do
    :: w < N ->
       sleeper[w] = false
       w = w + 1
    :: else -> break
    od
}

inline mcos_mfutex_one(w) {
    sleeper[w] = false
}

inline mcos_mfutex_wait() {
    assert(sleeper[_pid] == false);

    sleeper[_pid] = true;
    do
    :: sleeper[_pid] == true -> skip
    :: else -> break
    od
}

/****************************/

// MQ implementation
#define M_NUM 5
bit mq[M_NUM] = {0}
byte m_cnt = 0;

inline do_msg_enqueue(msg) {
    assert(mq[m_cnt] == 0);
    mq[m_cnt] = msg;
    m_cnt++
    assert(m_cnt <= M_NUM)
}

inline do_msg_dequeue(m_cnt) {
    m_cnt--;
    assert(mq[m_cnt] != 0);
    mq[m_cnt] = 0;
    assert(m_cnt >= 0)
}

// We must maintain concurrency at this level.
// Lock-free priorty queue could be the best one, but
// we only need emulate the thread-safe queue in this model.
inline msg_enqueue(msg) {
    d_step {
    if
    :: m_cnt == M_NUM -> mcos_mfutex_wait()
    :: else -> do_msg_enqueue(msg)
    fi
    }
}

inline msg_dequeue() {
    d_step {
    	if
    	:: m_cnt == 0 -> skip
    	:: m_cnt >= 1 ->
    	   do_msg_dequeue(m_cnt);
    	fi;
    }
}

// From here, the actual mq model for ensure
// that our user-space mq implemetation works well.
// All data-structures are put on the user-space and
// the queue and user_info are shared among the processes.
byte user_info[N*2] = {0}; // store MAX VAL
byte sleeper_cnt = 0;

inline register_sleeper_info(id) {
    // enqueue user info to ring buffer
    user_info[sleeper_cnt] = id;
    sleeper_cnt = (sleeper_cnt + 1) % (N * 2)
}

inline mq_send(msg) {
    msg_enqueue(msg);
    // dequeue
    mcos_mfutex_wake();
}

inline mq_receive() {
    do
    :: m_cnt >= 1 -> msg_dequeue()
    :: else ->
       register_sleeper_info(_pid);
       mcos_mfutex_wait()
    od
}

active[N] proctype producer() {
    mq_send(_pid + 1)
}

active[N] proctype consumer() {
    mq_receive()
}

