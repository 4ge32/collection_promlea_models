lfstack:
	spin -a $@.pml
	gcc pan.c
dynamic_allocation:
	spin -a $@.pml
	gcc pan.c
malloc:
	spin -a $@.h
	gcc pan.c
sleep:
	spin -a $@.pml
	gcc pan.c

queue:
	spin -a $@.h
	gcc pan.c
clean:
	rm -v pan.* *.pml.trail
