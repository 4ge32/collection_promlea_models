#include "lfstack.h"
#include <stdio.h>
#include <pthread.h>
_Atomic lfstack_t top = {0, NULL};
void *producer(void *input)
{
    for(int i=0; i<1000; i++)
    {
        push(&top, i);
        //printf("push %d\n",i);
    }
    pthread_exit(NULL);
}

void *consumer(void *input)
{
    for(int i=0; i<1000;)
    {
        int result;
        int dm;
        result = pop(&top);
        if(result == -1)
            //printf("the stack is empty\n");
            dm++;
        else
        {
            i++;
        }

    }
    pthread_exit(NULL);
}
int main()
{
    pthread_t tid[200];
    for(int i=0; i<100; i++)
        pthread_create(&tid[i],NULL,producer,NULL);
    for(int i=100; i<200; i++)
        pthread_create(&tid[i],NULL,consumer,NULL);
    for(int i=0; i<200; i++)
        pthread_join(tid[i],NULL);
    return 0;
}
