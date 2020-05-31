MODEL=435

all:
	spin -a ${MODEL}.pml
	gcc -DNP pan.c

run:
	./a.out -l

ded:
	spin -t -p ${MODEL}.pml

clean:
	rm -v pan.* ${MODEL}.pml.trail
