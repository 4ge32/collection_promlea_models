#ifndef __LFSTACK__
#define __LFSTACK__

void lf_push(void *data);
void *lf_pop(void);
void lf_init(void);
void lf_cleanup(void);

#endif
