MODEL=lfstack

all:
	spin -a ${MODEL}.pml
	gcc pan.c
tagp:
	spin -DTAGP -a ${MODEL}.pml
	gcc -DTAGP pan.c
ll_sc:
	spin -DLL_SC -a ${MODEL}.pml
	gcc -DLL_SC pan.c
vali:
	spin -t -p ${MODEL}.pml
clean:
	rm -v pan.* *.pml.trail
