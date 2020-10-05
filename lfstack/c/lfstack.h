#include <stdatomic.h>
#include <stdlib.h>

typedef struct _Node {
  int data;
  struct _Node *next;
} Node;

typedef struct _lfstack_t {
  unsigned int tag;
  Node *head;
} lfstack_t;

void push(_Atomic lfstack_t *lfstack, int value) {
  lfstack_t next;
  lfstack_t orig = atomic_load(lfstack);
  Node *node = malloc(sizeof(Node));
  node->data = value;
  do {
    node->next = orig.head;
    next.head = node;
#ifdef TAGP
    next.tag = orig.tag + 1;
#endif
  } while (!atomic_compare_exchange_weak(lfstack, &orig, next));
}

int pop(_Atomic lfstack_t *lfstack) {
  lfstack_t next;
  lfstack_t orig = atomic_load(lfstack);
  int ret;
  do {
    if (orig.head == NULL) {
      return -1;
    }
    next.head = orig.head->next;
#ifdef TAGP
    next.tag = orig.tag + 1;
#endif
  } while (!atomic_compare_exchange_weak(lfstack, &orig, next));
  ret = orig.head->data;
  free(orig.head);
  return ret;
}
