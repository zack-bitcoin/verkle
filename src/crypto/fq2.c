#include <erl_nif.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

//scalar field on top of bls12-381. used to implement jubjub.

//montgomery notation for fast multiplication.

//const uint64_t Max64 = 18446744073709551615U;

const uint64_t q[4] =
  {18446744069414584321U,
   6034159408538082302U,
   3691218898639771653U,
   8353516859464449352U};

uint64_t C[4];
int64_t arr[2];
int carry;

//add carry
#define ADD(A, B) (A + B + carry)
//the carry bit.
#define ADC(B, C) ((C<B) ||(carry && (C == B)))

//subtract borrow
#define SUB(A, B) (A - B - carry)
//the borrow bit. (stored in carry)
#define SBC(A, C) ((C>A)||(carry && (C == A)))

static int greater_than
(const uint64_t * a, const uint64_t * b)
{
  //actually greater than or equal to.
  for(int i = 3; i>=0; i--){
    if(a[i] > b[i]){return(1);}
    else if(a[i]<b[i]){return(0);}
  }
  return(1);
};

static void assume_positive_sub
(const uint64_t * a,
 const uint64_t * b,
 uint64_t * c){
  //assumes a >= b.
  //stores a-b in c.
  carry = 0;
  c[0] = SUB(a[0], b[0]);
  carry = SBC(a[0], c[0]);
  c[1] = SUB(a[1], b[1]);
  carry = SBC(a[1], c[1]);
  c[2] = SUB(a[2], b[2]);
  carry = SBC(a[2], c[2]);
  c[3] = SUB(a[3], b[3]);
};
static void assume_safe_add
(const uint64_t * a,
 const uint64_t * b,
 uint64_t *c){
  //assumes a + b < 2^64.
  //stores a+b in c.
  carry = 0;
  c[0] = ADD(a[0], b[0]);
  carry = ADC(b[0], c[0]);
  c[1] = ADD(a[1], b[1]);
  carry = ADC(b[1], c[1]);
  c[2] = ADD(a[2], b[2]);
  carry = ADC(b[2], c[2]);
  c[3] = ADD(a[3], b[3]);
};

ErlNifBinary BinA;
ErlNifBinary BinB;
ErlNifBinary resultnif;
static ERL_NIF_TERM setup
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  //only runs once at the beginning.
  enif_alloc_binary(32, &BinA);
  enif_alloc_binary(32, &BinB);
  enif_alloc_binary(32, &resultnif);
  return(argv[0]);
}

static void sub2
(int64_t * a, int64_t * b, int64_t * c)
{
  if(greater_than(a, b)){
    assume_positive_sub(a, b, c);
  } else {
    assume_positive_sub(q, b, c);
    assume_safe_add(c, a, c);
  } 
}

static void add2
(int64_t * a, int64_t * b, int64_t * c)
{
  assume_safe_add(a, b, c);

  if(carry){
    //a + b = 2^256 +c
    //want 2^256 + c - q
    assume_positive_sub(c, q, c);
  } else if(greater_than(c, q)){
    assume_positive_sub(c, q, c);
    //c - q
    //assume_positive_sub(a, b, c);
  } else {
    //assume_positive_sub(q, b, c);
    //assume_safe_add(c, a, c);
  } 
}

static ERL_NIF_TERM sub
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  enif_inspect_binary(env, argv[0], &BinA);
  enif_inspect_binary(env, argv[1], &BinB);

  sub2((uint64_t *)BinA.data,
              (uint64_t *)BinB.data, C);
  resultnif.data = (char *)C;

  return enif_make_binary(env, &resultnif);
}

static ERL_NIF_TERM add
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  enif_inspect_binary(env, argv[0], &BinA);
  enif_inspect_binary(env, argv[1], &BinB);

  add2((uint64_t *)BinA.data,
              (uint64_t *)BinB.data, C);
  resultnif.data = (char *)C;

  return enif_make_binary(env, &resultnif);
  
}



static ErlNifFunc nif_funcs[] =
  {
   {"sub", 2, sub},
   {"setup", 1, setup}
  };

ERL_NIF_INIT(fq2,nif_funcs,NULL,NULL,NULL,NULL)
