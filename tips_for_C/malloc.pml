#include "dynamic_allocation.pml"

inline malloc(ptr) {
    do_alloc(ptr)
}

inline free(ptr) {
    do_free(ptr)
}