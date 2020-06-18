/*
This file is generated by Cogent

*/

typedef void *SysState;
typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef struct unit_t {
            int dummy;
        } unit_t;
typedef struct bool_t {
            u8 boolean;
        } bool_t;
enum {
    LET_TRUE = 1,
} ;
enum {
    LETBANG_TRUE = 1,
} ;
enum untyped_func_enum {
    FUN_ENUM_inc,
    FUN_ENUM_inc_arr,
    FUN_ENUM_mul,
    FUN_ENUM_mul_bod,
    FUN_ENUM_sum,
    FUN_ENUM_sum_bod,
    FUN_ENUM_wordarray_fold_no_break_0,
    FUN_ENUM_wordarray_get_0,
    FUN_ENUM_wordarray_get_u32,
    FUN_ENUM_wordarray_length_0,
    FUN_ENUM_wordarray_length_u32,
    FUN_ENUM_wordarray_map_no_break_0,
    FUN_ENUM_wordarray_map_no_break_u32_0,
    FUN_ENUM_wordarray_put2_0,
    FUN_ENUM_wordarray_put2_u32,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t11;
typedef untyped_func_enum t12;
typedef untyped_func_enum t13;
typedef untyped_func_enum t14;
typedef untyped_func_enum t4;
typedef untyped_func_enum t15;
typedef untyped_func_enum t8;
typedef untyped_func_enum t16;
typedef struct t1 t1;
typedef struct t2 t2;
typedef struct t3 t3;
typedef struct t5 t5;
typedef struct t6 t6;
typedef struct t7 t7;
typedef struct t9 t9;
typedef struct t10 t10;
struct WordArray_u32 {
    int len;
    u32 *values;
} ;
typedef struct WordArray_u32 WordArray_u32;
struct t1 {
    WordArray_u32 *p1;
    u32 p2;
} ;
struct t2 {
    WordArray_u32 *arr;
    u32 idx;
    u32 val;
} ;
struct t3 {
    u32 elem;
    u32 acc;
    unit_t obsv;
} ;
struct t5 {
    WordArray_u32 *arr;
    u32 frm;
    u32 to;
    t4 f;
    u32 acc;
    unit_t obsv;
} ;
struct t6 {
    u32 elem;
    unit_t acc;
    unit_t obsv;
} ;
struct t7 {
    u32 p1;
    unit_t p2;
} ;
struct t9 {
    WordArray_u32 *arr;
    u32 frm;
    u32 to;
    t8 f;
    unit_t acc;
    unit_t obsv;
} ;
struct t10 {
    WordArray_u32 *p1;
    unit_t p2;
} ;
static inline u32 wordarray_get_0(t1);
static inline u32 wordarray_length_0(WordArray_u32 *);
static inline WordArray_u32 *wordarray_put2_0(t2);
static inline u32 wordarray_fold_no_break_0(t5);
static inline t10 wordarray_map_no_break_0(t9);
static inline __attribute__((pure)) u32 wordarray_get_u32(t1);
static inline __attribute__((pure)) u32 wordarray_length_u32(WordArray_u32 *);
static inline WordArray_u32 *wordarray_put2_u32(t2);
static inline t10 wordarray_map_no_break_u32_0(t9);
static inline __attribute__((const)) t7 inc(t6);
static inline t10 inc_arr(WordArray_u32 *);
static inline __attribute__((const)) u32 mul_bod(t3);
static inline __attribute__((pure)) u32 mul(WordArray_u32 *);
static inline __attribute__((const)) u32 sum_bod(t3);
static inline __attribute__((pure)) u32 sum(WordArray_u32 *);
static inline t10 dispatch_t11(untyped_func_enum a2, WordArray_u32 *a3)
{
    return inc_arr(a3);
}
static inline u32 dispatch_t12(untyped_func_enum a2, WordArray_u32 *a3)
{
    switch (a2) {
        
      case FUN_ENUM_mul:
        return mul(a3);
        
      case FUN_ENUM_sum:
        return sum(a3);
        
      case FUN_ENUM_wordarray_length_0:
        return wordarray_length_0(a3);
        
      default:
        return wordarray_length_u32(a3);
    }
}
static inline u32 dispatch_t13(untyped_func_enum a2, t1 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_get_0:
        return wordarray_get_0(a3);
        
      default:
        return wordarray_get_u32(a3);
    }
}
static inline WordArray_u32 *dispatch_t14(untyped_func_enum a2, t2 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_put2_0:
        return wordarray_put2_0(a3);
        
      default:
        return wordarray_put2_u32(a3);
    }
}
static inline u32 dispatch_t4(untyped_func_enum a2, t3 a3)
{
    switch (a2) {
        
      case FUN_ENUM_mul_bod:
        return mul_bod(a3);
        
      default:
        return sum_bod(a3);
    }
}
static inline u32 dispatch_t15(untyped_func_enum a2, t5 a3)
{
    return wordarray_fold_no_break_0(a3);
}
static inline t7 dispatch_t8(untyped_func_enum a2, t6 a3)
{
    return inc(a3);
}
static inline t10 dispatch_t16(untyped_func_enum a2, t9 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_map_no_break_0:
        return wordarray_map_no_break_0(a3);
        
      default:
        return wordarray_map_no_break_u32_0(a3);
    }
}
typedef u32 ErrCode;
typedef u32 WordArrayIndex;
typedef t6 inc_arg;
typedef WordArray_u32 *inc_arr_arg;
typedef t10 inc_arr_ret;
typedef t7 inc_ret;
typedef WordArray_u32 *mul_arg;
typedef t3 mul_bod_arg;
typedef u32 mul_bod_ret;
typedef u32 mul_ret;
typedef WordArray_u32 *sum_arg;
typedef t3 sum_bod_arg;
typedef u32 sum_bod_ret;
typedef u32 sum_ret;
typedef t5 wordarray_fold_no_break_0_arg;
typedef u32 wordarray_fold_no_break_0_ret;
typedef t1 wordarray_get_0_arg;
typedef u32 wordarray_get_0_ret;
typedef t1 wordarray_get_u32_arg;
typedef u32 wordarray_get_u32_ret;
typedef WordArray_u32 *wordarray_length_0_arg;
typedef u32 wordarray_length_0_ret;
typedef WordArray_u32 *wordarray_length_u32_arg;
typedef u32 wordarray_length_u32_ret;
typedef t9 wordarray_map_no_break_0_arg;
typedef t10 wordarray_map_no_break_0_ret;
typedef t9 wordarray_map_no_break_u32_0_arg;
typedef t10 wordarray_map_no_break_u32_0_ret;
typedef t2 wordarray_put2_0_arg;
typedef WordArray_u32 *wordarray_put2_0_ret;
typedef t2 wordarray_put2_u32_arg;
typedef WordArray_u32 *wordarray_put2_u32_ret;
static inline __attribute__((pure)) u32 wordarray_get_u32(t1 a1)
{
    t1 r2 = a1;
    u32 r3 = wordarray_get_0(r2);
    
    return r3;
}
static inline __attribute__((pure)) u32 wordarray_length_u32(WordArray_u32 *a1)
{
    WordArray_u32 *r2 = a1;
    u32 r3 = wordarray_length_0(r2);
    
    return r3;
}
static inline WordArray_u32 *wordarray_put2_u32(t2 a1)
{
    t2 r2 = a1;
    WordArray_u32 *r3 = wordarray_put2_0(r2);
    
    return r3;
}
static inline t10 wordarray_map_no_break_u32_0(t9 a1)
{
    t9 r2 = a1;
    t10 r3 = wordarray_map_no_break_0(r2);
    
    return r3;
}
static inline __attribute__((const)) t7 inc(t6 a1)
{
    u32 r2 = a1.elem;
    unit_t r3 = a1.acc;
    unit_t r4 = a1.obsv;
    u32 r5 = 1U;
    u32 r6 = r2 + r5;
    t7 r7 = (t7) {.p1 = r6, .p2 = r3};
    
    return r7;
}
static inline t10 inc_arr(WordArray_u32 *a1)
{
    WordArray_u32 *r2 = a1;
    u32 r3;
    
    if (LETBANG_TRUE)
        r3 = wordarray_length_0(r2);
    else
        ;
    
    u32 r4 = 0U;
    t8 r5 = FUN_ENUM_inc;
    unit_t r6 = (unit_t) {.dummy = 0};
    unit_t r7 = (unit_t) {.dummy = 0};
    t9 r8 = (t9) {.arr = r2, .frm = r4, .to = r3, .f = r5, .acc = r6, .obsv =
                  r7};
    t10 r9 = wordarray_map_no_break_u32_0(r8);
    
    return r9;
}
static inline __attribute__((const)) u32 mul_bod(t3 a1)
{
    u32 r2 = a1.elem;
    u32 r3 = a1.acc;
    unit_t r4 = a1.obsv;
    u32 r5 = r2 * r3;
    
    return r5;
}
static inline __attribute__((pure)) u32 mul(WordArray_u32 *a1)
{
    WordArray_u32 *r2 = a1;
    u32 r3 = wordarray_length_u32(r2);
    u32 r4 = 0U;
    t4 r5 = FUN_ENUM_mul_bod;
    u32 r6 = 0U;
    unit_t r7 = (unit_t) {.dummy = 0};
    t5 r8 = (t5) {.arr = r2, .frm = r4, .to = r3, .f = r5, .acc = r6, .obsv =
                  r7};
    u32 r9 = wordarray_fold_no_break_0(r8);
    
    return r9;
}
static inline __attribute__((const)) u32 sum_bod(t3 a1)
{
    u32 r2 = a1.elem;
    u32 r3 = a1.acc;
    unit_t r4 = a1.obsv;
    u32 r5 = r2 + r3;
    
    return r5;
}
static inline __attribute__((pure)) u32 sum(WordArray_u32 *a1)
{
    WordArray_u32 *r2 = a1;
    u32 r3 = wordarray_length_u32(r2);
    u32 r4 = 0U;
    t4 r5 = FUN_ENUM_sum_bod;
    u32 r6 = 0U;
    unit_t r7 = (unit_t) {.dummy = 0};
    t5 r8 = (t5) {.arr = r2, .frm = r4, .to = r3, .f = r5, .acc = r6, .obsv =
                  r7};
    u32 r9 = wordarray_fold_no_break_0(r8);
    
    return r9;
}
u16 u8_to_u16(u8 x)
{
    return (u16) x;
}
u32 u8_to_u32(u8 x)
{
    return (u32) x;
}
u64 u8_to_u64(u8 x)
{
    return (u64) x;
}
u8 u16_to_u8(u16 x)
{
    return (u8) x;
}
u32 u16_to_u32(u16 x)
{
    return (u32) x;
}
u8 u32_to_u8(u32 x)
{
    return (u8) x;
}
u16 u32_to_u16(u32 x)
{
    return (u16) x;
}
u64 u32_to_u64(u32 x)
{
    return (u64) x;
}
u32 u64_to_u32(u64 x)
{
    return (u32) x;
}
u8 u64_to_u8(u64 x)
{
    return (u8) x;
}
u16 u64_to_u16(u64 x)
{
    return (u16) x;
}
u32 wordarray_get_0(t1 args)
{
    if (args.p2 >= args.p1->len)
        return 0;
    return args.p1->values[args.p2];
}
u32 wordarray_length_0(WordArray_u32 *array)
{
    return array->len;
}
t10 wordarray_map_no_break_0(t9 args)
{
    t10 ret;
    t6 fargs;
    t7 fret;
    u32 to = args.to > args.arr->len ? args.arr->len : args.to;
    u32 i;
    
    fargs.acc = args.acc;
    fargs.obsv = args.obsv;
    for (i = args.frm; i < to; i++) {
        fargs.elem = args.arr->values[i];
        fret = dispatch_t8(args.f, fargs);
        args.arr->values[i] = fret.p1;
        fargs.acc = fret.p2;
    }
    ret.p1 = args.arr;
    ret.p2 = fargs.acc;
    return ret;
}
u32 wordarray_fold_no_break_0(t5 args)
{
    t3 fargs;
    u32 to = args.to > args.arr->len ? args.arr->len : args.to;
    u32 i;
    
    fargs.obsv = args.obsv;
    fargs.acc = args.acc;
    for (i = args.frm; i < to; i++) {
        fargs.elem = args.arr->values[i];
        fargs.acc = dispatch_t4(args.f, fargs);
    }
    return fargs.acc;
}
WordArray_u32 *wordarray_put2_0(t2 args)
{
    if (__builtin_expect(!!(args.idx < args.arr->len), 1))
        args.arr->values[args.idx] = args.val;
    return args.arr;
}

