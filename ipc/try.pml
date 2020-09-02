byte a = 0;
active proctype thread() {
	do
	::
		if
		:: a = 1;
		:: a = 2;
		fi;
		if
		:: a == 2 -> printf("reach a == 2!\n")
		:: else -> break
		fi
	printf("a = %d\n", a);
	od
}
