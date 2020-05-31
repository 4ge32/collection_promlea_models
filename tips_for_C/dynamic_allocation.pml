/*
 struct person{
    int age;
 };

 struct person *ptr;
 ptr = malloc(sizeof(struct person));
*/
typedef person {
    int age;
}

person person_mem[9];
int person_valid[9];

int person_ct;
int ptr;
int tmp;

inline do_alloc(ptr) {
    atomic {
        person_ct = 1;
        do
        :: (person_ct >= 9) -> break
        :: else ->
            if
            :: (person_valid[person_ct] == 0) ->
            person_valid[person_ct] = 1;
            break
            :: else -> person_ct ++
            fi
        od;
        assert (person_ct < 9);
        tmp = person_ct;
        person_ct = 1
    };
    ptr = tmp;
}

inline free(ptr) {
    d_step {
        person_valid[ptr] = 0;
        person_mem[ptr].age = 0
    };
}

active proctype alloc() {
    do_alloc(ptr);
    person_mem[ptr].age = 24;
    free(ptr);
}
