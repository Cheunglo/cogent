// This file is generated by Cogent

#include "sub-yes.h"

extern t1 foo(t1 a1)
{
    t1 r2;
    
    if (a1.tag == TAG_ENUM_A) {
        u32 r3 = 42U;
        bool_t r4 = (bool_t) {.boolean = a1.A != r3};
        t1 r5;
        
        r5 = (t1) {.tag = TAG_ENUM_B, .B = r4};
        
        t1 r6 = r5;
        
        r2 = r6;
    } else {
        t1 r7 = a1;
        
        r2 = r7;
    }
    
    t1 r8 = r2;
    
    return r8;
}

