CC=gcc
CPP=g++
W=-Wall -Wextra

all:
	$(CC) -c lfq.c -latomic -lpthread $(W)
	$(CC) -c lfs.c -latomic $(W)
	$(CPP) -c test.cpp $(W)
	$(CPP) lfq.o lfs.o test.o -lpthread -latomic $(W)



