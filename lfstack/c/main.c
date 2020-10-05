#include "lfstack.h"
#include <pthread.h>
#include <stdio.h>

_Atomic lfstack_t top = {0, NULL};
#define N 100
#define M 2000
int res[N * M];
_Atomic int res_cnt = 0;

int compare_int(const void *a, const void *b) {
  if (*(int*)a > *(int*)b)
    return 1;
  else if (*(int*)a < *(int*)b) {
    return -1;
  } else {
    return 0;
  }
}

void *producer(void *input) {
  for (int i = 0; i < M; i++) {
    push(&top, i + (((int)input) * M));
  }
  pthread_exit(NULL);
}

void *consumer(void *input) {
  for (int i = 0; i < M; i++) {
    int result = 0;
  again:
    result = pop(&top);
    if (result == -1) {
      goto again;
    } else {
      res[atomic_fetch_add(&res_cnt, 1)] = result;
    }
  }
  pthread_exit(NULL);
}

int main() {
  pthread_t tid[N * 2];
  int i, j;
  for (i = 0; i < N; i++)
    pthread_create(&tid[i], NULL, producer, (void *)i);
  for (j = N; j < N * 2; j++)
    pthread_create(&tid[j], NULL, consumer, (void *)j);
  for (int k = 0; k < N * 2; k++)
    pthread_join(tid[k], NULL);
  qsort(res, N * M, sizeof(int), compare_int);
  for (int i = 0; i < N * M; i++) {
     if (res[i] != i) {
      printf("%d vs %d\n", res[i], i);
      return -1;
    }
  }
  return 0;
}
