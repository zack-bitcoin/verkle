#include <erl_nif.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

//scalar field on top of bls12-381. used to implement jubjub.

//montgomery notation for fast multiplication.

const uint32_t Max32 = 4294967295U;
const uint32_t q[8] =
  {1,
   4294967295,
   4294859774,
   1404937218,
   161601541,
   859428872,
   698187080,
   1944954707};
   
//uint32_t A[8];
//uint32_t B[8];
uint32_t C[8];
int carry = 0;
int32_t arr[2];
//unsigned char resultchars[32];
ErlNifBinary resultnif;

//BinA and BinB are the 2 inputs for binary operations.
ErlNifBinary BinA;
ErlNifBinary BinB;
unsigned char bin2[32];


//add carry
//uint64_t d;
uint32_t d;
void adc
(uint32_t a, uint32_t b, uint32_t c,
 uint32_t arr[])
{
  d = a;
  d += b;
  d += c;
  arr[0] = d;//value
  //arr[1] = d >> 32;//carry
  arr[1] = d < a;//carry
}


//subtract borrow
uint32_t e;
void sbb
(uint32_t a, uint32_t b, uint32_t borrow,
 uint32_t arr[])
{
  e = b;
  e += borrow;
  //printf("subtracting %lu %lu \n", d, e);
  arr[0] = a - e;
  arr[1] = (a < e);
}

int greater_than(const uint32_t * a,
                 const uint32_t * b)
{
  for(int i = 7; i>=0; i--){
    if(a[i] > b[i]){return(1);}
    else if(a[i]<b[i]){return(0);}
  }
  return(1);
};

void assume_positive_sub
(const uint32_t * a,
 const uint32_t * b,
 uint32_t * c){
  //assumes a >= b.
  //stores a-b in c.
  carry = 0;
  for(int i = 0; i<8; i++){
    sbb(a[i], b[i], carry, arr);
    carry = arr[1];
    c[i] = arr[0];
  };
};
void assume_safe_add
(const uint32_t * a,
 const uint32_t * b,
 uint32_t *c){
  carry = 0;
  for(int i = 0; i<8; i++){
    adc(a[i], b[i], carry, arr);
    carry = arr[1];
    c[i] = arr[0];
  };
};
static ERL_NIF_TERM setup
(ErlNifEnv* env,
 int argc,
 const ERL_NIF_TERM argv[])
{
  //only runs once at the beginning.
  int result = enif_alloc_binary
    (32, &BinA);
  int result2 = enif_alloc_binary
    (32, &BinB);
  int result3 = enif_alloc_binary
    (32, &resultnif);

  return(argv[0]);
}

void sub2(int32_t * a, int32_t *b, int32_t * c)
{
  if(greater_than(a, b)){
    assume_positive_sub(a, b, c);
  } else {
    assume_positive_sub(q, b, c);
    assume_safe_add(c, a, c);
  } 
}

//todo. maybe instead of memcopy, we can just move pointers around.

static ERL_NIF_TERM sub(ErlNifEnv* env,
                        int argc,
                        const ERL_NIF_TERM argv[])
{

  enif_inspect_binary(env, argv[0], &BinA);
  enif_inspect_binary(env, argv[1], &BinB);

  sub2((uint32_t *)BinA.data,
       (uint32_t *)BinB.data, C);
  resultnif.data = (char *)C;
  

  ERL_NIF_TERM finalresult = enif_make_binary//0.05
    (env, &resultnif);
  return finalresult;
}


static ErlNifFunc nif_funcs[] =
  {
   {"sub", 2, sub},
   {"setup", 1, setup}
  };

ERL_NIF_INIT(fq2,nif_funcs,NULL,NULL,NULL,NULL)
