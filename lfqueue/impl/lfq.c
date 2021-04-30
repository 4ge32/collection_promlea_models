#include "lfs.h"
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define BUILD_BUG_ON(condition) ((void)sizeof(char[1 - 2 * !!(condition)]))
#define BUG printf("%s: %d\n", __func__, __LINE__)
#define FATAL                                                                  \
  printf("%s: %d(FATAL)\n", __func__, __LINE__);                               \
  while (1)

typedef struct _qnode {
  struct _qnode *next;
  long entry;
  uint64_t pos;
} qnode_t;

typedef struct {
  qnode_t *head;
  qnode_t *tail;
} lfqueue_t;

/* For fully lock-free algorithm, this value shall be over the number of threads
 * which the queue use
 */
#define LNUM 51
lfqueue_t *queue;
static long nf = 0;             /* count not freed ptr for debugging */
static uintptr_t PTE[LNUM];     /* Per Thread Entry, not Page Table Entry */
static pthread_t PTE_MAP[LNUM]; /* Manage PTE entry mapping */
static void register_ptr(void *ptr) { lf_push(ptr); }

/* Safely free pointer in lock-free manner.
 * To achieve full lock-free, use lock-free stack.
 */
static void safe_free(void) {
  void *ret;
  do {
    ret = lf_pop();
    if (ret != NULL) {
      _Bool is_free = true;
      for (uint_fast8_t j = 0; j < LNUM; ++j) {
        if ((uintptr_t)ret == PTE[j]) {
          is_free = false;
          break;
        }
      }
      if (is_free) {
        free(ret);
        atomic_fetch_add(&nf, -1);
      } else {
        lf_push(ret);
        break;
      }
    }
  } while (ret != NULL);
}

/**
 * @brief Enqueue a object in lock-free manner
 *
 * @param num The object will be enqueued
 * @return int return 0 if success, otherwise return -1
 */
int32_t enqueue(long entry) {
  /* Allocate and setup a new object */
  qnode_t *node = malloc(sizeof(qnode_t));
  if (node == NULL) {
    return -1;
  }
  node->entry = entry;
  node->next = NULL;

  /* Insert a new entry */
  qnode_t *old_tail = atomic_exchange(&queue->tail, node);
  old_tail->next = node;
  atomic_thread_fence(memory_order_seq_cst);

  return 0;
}

/**
 * @brief make per thread entry map clean.
 *
 * @param arg The argument is from pthread_exit().
 */
void pte_map_cleanup(void *arg) {
  pthread_t tid = *(pthread_t *)arg;

  for (uint_fast8_t idx = 0; idx < LNUM; ++idx) {
    if (PTE_MAP[idx] == tid) {
      atomic_store(&PTE_MAP[idx], 0);
    }
  }
}

/**
 * @brief Get the local slot to declare that
 * I am now trying to dequeue the entry.
 * After success, one of PTE is marked as used by the specified
 * thread id's thread.
 * If LNUM is lower than the number of consumer thread,
 * the function will be the same work of spin-lock.
 * Otherwise, all of consumer thread can finally get the PTE slot in lock-free
 * manner.
 *
 * @param tid thread id
 * @return uintptr_t* Return Per Thread Entry pointer
 */
uintptr_t *get_local(pthread_t tid) {
  /* Mapping thread id and PTE to store thread-local data */
  uint_fast8_t idx;
  _Bool comp = false;

  do {
    for (idx = 0; idx < LNUM; ++idx) {
      uintptr_t ent = atomic_load(&PTE_MAP[idx]);
      if (ent == 0) {
        comp = atomic_compare_exchange_strong(&PTE_MAP[idx], &ent, tid);
        if (comp == true) {
          break;
        }
      }
    }
  } while (comp == false);

  return &PTE[idx];
}

/**
 * @brief Dequeue a object in lock-free manner
 *
 * @return int The gotten object
 */
int dequeue(void) {
  int ret;
  _Bool comp = false;
  qnode_t *old_head, *new_head;
  pthread_t tid = pthread_self();

  pthread_cleanup_push(pte_map_cleanup, (void *)&tid);
  uintptr_t *local = get_local(tid);

  do {
    /* Declare that I will start refereceing the node */
    *local = (uintptr_t)atomic_load(&queue->head);

    /* The section of refering the node starts */

    /* Use the pointer which storing per thread entry */
    old_head = (qnode_t *)*local;

    /* head is the same as tail, means that there is no node */
    if (old_head == atomic_load(&queue->tail)) {
      *local = 0;
      break;
    }

    /* head has already changed.
     * I guess that this func is useful for optimization
     * under something like time-slice scheduling,
     * but won't often do useful work under SCHED_FIFO scheduling.
     */
    if (old_head != queue->head) {
      continue;
    }

    /* Producer has not updated the linked list.
     * Queue tail has already updated by producers, but
     * actual inserting has not been done yet.
     */
    new_head = old_head->next;
    if (new_head == NULL) {
      continue;
    }

    /* Copy entry material first. If copying after cas,
     * there is a possiblity that other threads
     * refer and free it.
     */
    ret = new_head->entry;

    comp = atomic_compare_exchange_strong(&queue->head, &old_head, new_head);
    /* The section of refering the node finish if CAS fails */
  } while (comp == false);

  /* The section of refering the node finish if CAS success or look break */
  *local = 0;

  if (comp == true) {
    if (ret < 0) {
      FATAL;
    }

    /* Now, the other thread cannot observe
     * old_head because the above CAS disconnect it.
     * Only the threads already having the pointer
     * has a possiblity to dereference it.
     * The threads loaded the pointer to their lcal
     * PTE firstly before starting refer the node.
     * Therefore, let's traverse them.
     */
    _Bool is_free = true;
    atomic_thread_fence(memory_order_seq_cst);

    for (uint_fast8_t i = 0; i < LNUM; ++i) {
      if ((uintptr_t)old_head == PTE[i]) {
        is_free = false;
        break;
      }
    }

    if (is_free) {
      free(old_head);
    } else {
      atomic_fetch_add(&nf, 1);
      register_ptr(old_head);
    }
  } else {
    ret = -1;
  }

  safe_free();
  pthread_cleanup_pop(1);

  return ret;
}

void lfq_init(void) {
  BUILD_BUG_ON(LNUM > UINT8_MAX);
  queue = malloc(sizeof(lfqueue_t));
  qnode_t *dummy = malloc(sizeof(qnode_t));
  /* Prepare first dummy node */
  queue->head = dummy;
  queue->tail = dummy;
  dummy->next = NULL;
  dummy->entry = -1;

  /* Init lock-free stack for managing not freed ptr */
  lf_init();
}

void lfq_cleanup(void) {
  /* No need to cleanup lfq resources because
   * all of them is stored communication channel object.
   * When destroying them, all of resources return to
   * Kernel.
   */
}

void con_(void) {
  if (nf != 0) {
    FATAL;
  }
}
