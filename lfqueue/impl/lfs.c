#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct _snode {
  struct _snode *next;
  void *data;
} snode_t;

typedef struct {
  snode_t *head;
  int tag;
} lfstack_t;

lfstack_t *stack;

void lf_push(void *data) {
  lfstack_t new_head;
  lfstack_t orig;
  _Bool comp;

  orig = atomic_load(stack);

  snode_t *node = malloc(sizeof(snode_t));
  if (node == NULL) {
    /* For product level code, we should reserve the same size allocation memory
     * area with lock-free queue use, and do alloc by my_alloc().
     * By doing it, malloc for managing not freed pointer will have enough
     * memory area. Therefore, no possiblity that malloc returns NULL.
     */
    printf("FATAL\n");
  }
  node->data = data;

  do {
    node->next = orig.head;
    new_head.head = node;
    new_head.tag = orig.tag + 1;
    comp = atomic_compare_exchange_strong(stack, &orig, new_head);
  } while (comp == false);
}

void *lf_pop(void) {
  lfstack_t next;
  lfstack_t orig;
  _Bool comp;
  void *ret = NULL;

  orig = atomic_load(stack);
  do {
    if (orig.head == NULL) {
      return NULL;
    }
    next.head = orig.head->next;
    next.tag = orig.tag + 1;
    comp = atomic_compare_exchange_strong(stack, &orig, next);
  } while (comp == false);

  ret = orig.head->data;
  free(orig.head);

  return ret;
}

void lf_init(void) {
  stack = malloc(sizeof(lfstack_t));
  stack->head = NULL;
  stack->tag = 0;
}

void lf_cleanup(void) { free(stack); }
