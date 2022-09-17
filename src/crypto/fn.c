#include <erl_nif.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

//scalar field on top of secp256k1.
//uses montgomery multiplication.

//order of the group on top of secp256k1.
//115792089237316195423570985008687907852837564279074904382605163141518161494337
const uint64_t q[4] =
{13822214165235122497U,13451932020343611451U,
 18446744073709551614U,18446744073709551615U};
//<<A:64/little, B:64/little, C:64/little, D:64/little>> = <<Q:256/little>>.

//<<A:64, B:64, C:64, D:64>> = reverse_bytes(fr:encode(1)).
const uint64_t one[4] =
  {0U,1U,4994812053365940164U,4624529908474429119U};

const uint64_t zero[4] =
  {0U,0U,0U,0U};


//-(q^-1 mod 2^64) mod 2^64
const uint64_t INV = 5408259542528602431U;

//subtract borrow
#define SUB(A, B, car) (A - B - car)
//add carry
#define ADC(a, b, c, car) {c = a + b + car; car = ((c < b) || (car && (c == b)));}

#define ADC2(a, b, car, c, car2) {c = a + b + car; car2 = ((c < b) || (car && (c == b)));}

static inline int greater_than
(const uint64_t * a, const uint64_t * b)
{
  //actually greater than or equal to.
  for(int i = 3; i>=0; i--){
    if(a[i] > b[i]){return(1);}
    else if(a[i]<b[i]){return(0);}
  }
  return(1);
};

//__uint128_t prod;
static inline void mac
(const uint64_t a, const uint64_t b,
 const uint64_t c, const uint64_t mac_carry,
 uint64_t * result, uint64_t * next_carry) {
  //a + (b * c) + carry
  __uint128_t prod =
    (__uint128_t)mac_carry + (__uint128_t)a +
    ((__uint128_t)b * (__uint128_t)c);
  *result = prod;
  *next_carry = prod >> 64;
}

static inline void subtract64
(const uint64_t * a,
 const uint64_t * b,
 uint64_t * c){
  //sometimes a and b are the same array, so we need to calculate the carries first.

  int carry1 = a[0] < b[0];
  int carry2 = a[1] < b[1];
  int carry3 = a[2] < b[2];
  
  c[0] = SUB(a[0], b[0], 0);
  c[1] = SUB(a[1], b[1], carry1);
  c[2] = SUB(a[2], b[2], carry2);
  c[3] = SUB(a[3], b[3], carry3);
};
static inline void addition64
(const uint64_t * a,
 const uint64_t * b,
 uint64_t *c,
 uint * carrystart){
  //stores a+b in c.
  ADC(a[0], b[0], c[0], *carrystart);
  ADC(a[1], b[1], c[1], *carrystart);
  ADC(a[2], b[2], c[2], *carrystart);
  ADC(a[3], b[3], c[3], *carrystart);
};

static inline void neg2
(uint64_t * a, uint64_t * c)
{
  subtract64(q, a, c);
};

static inline void sub2
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //c = (a-b) mod ?q

  if(greater_than(a, b)){
    subtract64(a, b, c);//c=a-b
  } else {
    subtract64(q, b, c);//c=q-b
    int subcarry = 0;
    addition64(c, a, c, &subcarry);//c=c+a
  } 
}

static inline void add2
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //c = (a+b) mod ?q

  int addcarry = 0;
  addition64(a, b, c, &addcarry);//c = a+b;
  if(addcarry || greater_than(c, q)){
    subtract64(c, q, c);//c = c-q
  }
}

//uint64_t mulcarry;
static inline void multiply64
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //a is 256 bits, b is 256 bits, c is 512 bits.
  //c = a * b.
  uint64_t mulcarry = 0;
  mac(0, a[0], b[0], mulcarry, &c[0], &mulcarry);
  mac(0, a[0], b[1], mulcarry, &c[1], &mulcarry);
  mac(0, a[0], b[2], mulcarry, &c[2], &mulcarry);
  mac(0, a[0], b[3], mulcarry, &c[3], &c[4]);

  mulcarry = 0;
  mac(c[1], a[1], b[0], mulcarry, &c[1],&mulcarry);
  mac(c[2], a[1], b[1], mulcarry, &c[2],&mulcarry);
  mac(c[3], a[1], b[2], mulcarry, &c[3],&mulcarry);
  mac(c[4], a[1], b[3], mulcarry, &c[4],&c[5]);
  
  mulcarry = 0;
  mac(c[2], a[2], b[0], mulcarry, &c[2],&mulcarry);
  mac(c[3], a[2], b[1], mulcarry, &c[3],&mulcarry);
  mac(c[4], a[2], b[2], mulcarry, &c[4],&mulcarry);
  mac(c[5], a[2], b[3], mulcarry, &c[5],&c[6]);

  mulcarry = 0;
  mac(c[3], a[3], b[0], mulcarry, &c[3],&mulcarry);
  mac(c[4], a[3], b[1], mulcarry, &c[4],&mulcarry);
  mac(c[5], a[3], b[2], mulcarry, &c[5],&mulcarry);
  mac(c[6], a[3], b[3], mulcarry, &c[6],&c[7]);
}


static inline void redc(uint64_t * r, uint64_t * c)
{
  uint64_t mulcarry = 0;
  //uint64_t mulcarry2 = 0;
  uint mulcarry2 = 0;
  uint64_t k;

  k = r[0] * INV;
  mac(r[0], k, q[0], 0, &c[0], &mulcarry);
  mac(r[1], k, q[1], mulcarry, &r[1], &mulcarry);
  mac(r[2], k, q[2], mulcarry, &r[2], &mulcarry);
  mac(r[3], k, q[3], mulcarry, &r[3], &mulcarry);
  ADC2(r[4], mulcarry, 0, r[4], mulcarry2);

  k = r[1] * INV;
  mac(r[1], k, q[0], 0, &c[0], &mulcarry);
  mac(r[2], k, q[1], mulcarry, &r[2], &mulcarry);
  mac(r[3], k, q[2], mulcarry, &r[3], &mulcarry);
  mac(r[4], k, q[3], mulcarry, &r[4], &mulcarry);
  ADC2(r[5], mulcarry, mulcarry2, r[5], mulcarry2);

  k = r[2] * INV;
  mac(r[2], k, q[0], 0, &c[0], &mulcarry);
  mac(r[3], k, q[1], mulcarry, &r[3], &mulcarry);
  mac(r[4], k, q[2], mulcarry, &r[4], &mulcarry);
  mac(r[5], k, q[3], mulcarry, &r[5], &mulcarry);
  ADC2(r[6], mulcarry, mulcarry2, r[6], mulcarry2);

  k = r[3] * INV;
  mac(r[3], k, q[0], 0, &c[0], &mulcarry);
  mac(r[4], k, q[1], mulcarry, &r[4], &mulcarry);
  mac(r[5], k, q[2], mulcarry, &r[5], &mulcarry);
  mac(r[6], k, q[3], mulcarry, &r[6], &mulcarry);
  ADC(r[7], mulcarry, r[7], mulcarry2);

  uint64_t * tmq2 = &r[4];
  if(greater_than(tmq2, q)){
    subtract64(tmq2, q, c);
  } else {
    memcpy(c, tmq2, 32);//there is probably a way to do this with only sending pointers around.
  }
};

static inline void square2
(uint64_t * a, uint64_t * b)
{
  uint64_t r[8];
  uint64_t carry;
  mac(0, a[0], a[1], 0, &r[1], &carry);
  mac(0, a[0], a[2], carry, &r[2], &carry);
  mac(0, a[0], a[3], carry, &r[3], &r[4]);

  mac(r[3], a[1], a[2], 0, &r[3], &carry);
  mac(r[4], a[1], a[3], carry, &r[4], &r[5]);

  mac(r[5], a[2], a[3], 0, &r[5], &r[6]);

  r[7] = r[6] >> 63;
  r[6] = (r[6] << 1) | (r[5] >> 63);
  r[5] = (r[5] << 1) | (r[4] >> 63);
  r[4] = (r[4] << 1) | (r[3] >> 63);
  r[3] = (r[3] << 1) | (r[2] >> 63);
  r[2] = (r[2] << 1) | (r[1] >> 63);
  r[1] = (r[1] << 1);

  mac(0, a[0], a[0], 0, &r[0], &carry);
  ADC2(r[1], carry, 0, r[1], carry);
  mac(r[2], a[1], a[1], carry, &r[2], &carry);
  ADC2(r[3], carry, 0, r[3], carry);
  mac(r[4], a[2], a[2], carry, &r[4], &carry);
  ADC2(r[5], carry, 0, r[5], carry);
  mac(r[6], a[3], a[3], carry, &r[6], &carry);
  ADC2(r[7], carry, 0, r[7], carry);

  redc(r, b);
}

static inline void mul2
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  uint64_t mul2_r[8];
  multiply64(a, b, mul2_r);
  redc(mul2_r, c);
}
static void short_pow2
(uint64_t * a, uint64_t b, uint64_t * c)
{
  //uint64_t acc[4];
  memcpy(c, one, 32);
  while(b > 0){
    if((b % 2) == 1){
      mul2(c, a, c);
    }
    square2(a, a);
    b = b >> 1;
  };
  //memcpy(a, acc, 32);
}
static void pow3
(uint64_t * c, uint64_t b, uint64_t * acc)
{
  for(int i = 64; i > 0; i--){
    if((b % 2) == 1){
      mul2(acc, c, acc);
    }
    square2(c, c);
    b = b >> 1;
  }
};
static void pow2
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  memcpy(c, one, 32);
  uint64_t A[4];
  memcpy(A, a, 32);
  pow3(A, b[0], c);
  pow3(A, b[1], c);
  pow3(A, b[2], c);
  pow3(A, b[3], c);
}

static ERL_NIF_TERM error_atom
(ErlNifEnv* env)
{  
    const char * msg = "error";
    ERL_NIF_TERM Error =
      enif_make_atom(env, msg);
    return(Error);
}

static ERL_NIF_TERM neg
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  if(!(argc == 1)){
    return(error_atom(env));
  }
  ErlNifBinary A;
  int check =
    enif_inspect_binary(env, argv[0], &A);
  if((!check) || (!(A.size == 32))){
    return(error_atom(env));
  };
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 32, &Result);
  neg2((uint64_t *)A.data,
       (uint64_t *)C);
  enif_release_binary(&A);
  return(Result);
}
static ERL_NIF_TERM sub
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  if(!(argc == 2)){
    return(error_atom(env));
  }
  ErlNifBinary BinAi;
  ErlNifBinary BinBi;
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 32, &Result);
  int checka =
    enif_inspect_binary(env, argv[0], &BinAi);
  int checkb =
    enif_inspect_binary(env, argv[1], &BinBi);

  if((!checka) || (!(BinAi.size == 32))){
    return(error_atom(env));
  };
  if((!checkb) || (!(BinBi.size == 32))){
    return(error_atom(env));
  };
  
  sub2((uint64_t *)BinAi.data,
       (uint64_t *)BinBi.data,
       (uint64_t *)C);//~0.007
  enif_release_binary(&BinAi);
  enif_release_binary(&BinBi);
  return Result;
}

static ERL_NIF_TERM add
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary BinAi;
  ErlNifBinary BinBi;
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 32, &Result);
  int checka =
    enif_inspect_binary(env, argv[0], &BinAi);
  int checkb =
    enif_inspect_binary(env, argv[1], &BinBi);
  if((!checka) || (!(BinAi.size == 32))){
    return(error_atom(env));
  };
  if((!checkb) || (!(BinBi.size == 32))){
    return(error_atom(env));
  };
  add2((uint64_t *)BinAi.data,
       (uint64_t *)BinBi.data,
       (uint64_t *)C);
  enif_release_binary(&BinAi);
  enif_release_binary(&BinBi);
  return(Result);
}
static ERL_NIF_TERM mul
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary BinAi;
  ErlNifBinary BinBi;
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 32, &Result);
  int checka =
    enif_inspect_binary(env, argv[0], &BinAi);
  int checkb =
    enif_inspect_binary(env, argv[1], &BinBi);
  if((!checka) || (!(BinAi.size == 32))){
    return(error_atom(env));
  };
  if((!checkb) || (!(BinBi.size == 32))){
    return(error_atom(env));
  };
  mul2((uint64_t *)BinAi.data,
       (uint64_t *)BinBi.data,
       (uint64_t *)C);
  enif_release_binary(&BinAi);
  enif_release_binary(&BinBi);
  return Result;
};
static ERL_NIF_TERM square
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary BinAi;
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 32, &Result);
  int checka =
    enif_inspect_binary(env, argv[0], &BinAi);
  if((!checka) || (!(BinAi.size == 32))){
    return(error_atom(env));
  };
  square2((uint64_t *)BinAi.data,
          (uint64_t *)C);
  enif_release_binary(&BinAi);
  return Result;
};
static ERL_NIF_TERM power
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary A, B;
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 32, &Result);
  int checka =
    enif_inspect_binary(env, argv[0], &A);
  int checkb =
    enif_inspect_binary(env, argv[1], &B);
  if((!checka) || (!(A.size == 32))){
    return(error_atom(env));
  };
  if((!checkb) || (!(B.size == 32))){
    return(error_atom(env));
  };
  pow2((uint64_t *)A.data,
       (uint64_t *)B.data,
       (uint64_t *)C);
  enif_release_binary(&A);
  enif_release_binary(&B);
  memcpy(C, one, 32);
  return Result;
};
static ERL_NIF_TERM short_power
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary A;
  ErlNifUInt64 B;
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 32, &Result);
  int checka =
    enif_inspect_binary(env, argv[0], &A);
  int checkb =
    enif_get_uint64(env, argv[1], &B);
  if((!checka) || (!(A.size == 32))){
    return(error_atom(env));
  };
  if((!checkb)){
    return(error_atom(env));
  };
  short_pow2((uint64_t *)A.data,
             (uint64_t) B,
             (uint64_t *)C);
  enif_release_binary(&A);
  return Result;
};
/*
static ERL_NIF_TERM inv
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary BinAi;
                                       
  enif_inspect_binary(env, argv[0], &BinAi);
  inv2((uint64_t *)BinAi.data,
       (uint64_t *)BinAi.data);
  return enif_make_binary(env, &BinAi);
};
*/
static ERL_NIF_TERM ctest
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  //enif_inspect_binary(env, argv[0], &BinA);
  //resultnif.data = (char *)BinA.data;
    //resultnif.data = (char *)C;
  //return enif_make_binary(env, &resultnif);
  return argv[0];
}


static ErlNifFunc nif_funcs[] =
  {
   {"neg", 1, neg},
   {"sub", 2, sub},
   {"add", 2, add},
   {"mul", 2, mul},
   {"square", 1, square},
   {"pow", 2, power},
   {"short_pow", 2, short_power},

   {"ctest", 1, ctest},
  };

ERL_NIF_INIT(fn,nif_funcs,NULL,NULL,NULL,NULL)
