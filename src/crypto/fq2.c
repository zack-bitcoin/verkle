#include <erl_nif.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

//scalar field on top of bls12-381. used to implement jubjub.
//uses montgomery notation for fast multiplication.

//prime used for the scalar field on top of jubjub.
const uint64_t q[4] =
  {18446744069414584321U,
   6034159408538082302U,
   3691218898639771653U,
   8353516859464449352U};

//q*iq mod 2^256 = -1
const uint64_t iq[4] = 
{18446744069414584319U,
 6033235805885848573U,
 1737030558577650694U,
 4414718065938212921U};

//-(q^-1 mod 2^64) mod 2^64
//ffff_fffe_ffff_ffff
//FFFFFFFEFFFFFFFF
const uint64_t INV = 18446744069414584319U;
//18446744073441116159 other endian?

//uint64_t C[4];
//uint64_t arr[2];
//int carry;

//add carry
#define ADD(A, B, car) (A + B + car)
//the carry bit.
#define ADC(B, C, car) ((C<B) ||(car && (C == B)))

//subtract borrow
#define SUB(A, B, car) (A - B - car)

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

//__uint128_t prod;
static void mac
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

static void subtract64
(const uint64_t * a,
 const uint64_t * b,
 uint64_t * c){
  int carry = 0;
  int nextcarry = 0;
  carry = 0;
  nextcarry = (a[0] < b[0]);
  c[0] = SUB(a[0], b[0], carry);
  carry = nextcarry;
  nextcarry = (a[1] < b[1]);
  c[1] = SUB(a[1], b[1], carry);
  carry = nextcarry;
  nextcarry = (a[2] < b[2]);
  c[2] = SUB(a[2], b[2], carry);
  carry = nextcarry;
  nextcarry = (a[3] < b[3]);
  c[3] = SUB(a[3], b[3], carry);
  //stores a-b in c.
  //c[0] = SUB(a[0], b[0], 0);
  //c[1] = SUB(a[1], b[1], a[0] < b[0]);
  //c[2] = SUB(a[2], b[2], a[1] < b[1]);
  //c[3] = SUB(a[3], b[3], a[2] < b[2]);
};
static void addition64
(const uint64_t * a,
 const uint64_t * b,
 uint64_t *c,
 int * carrystart){
  //stores a+b in c.
  c[0] = ADD(a[0], b[0], *carrystart);
  *carrystart = ADC(b[0], c[0], *carrystart);
  c[1] = ADD(a[1], b[1], *carrystart);
  *carrystart = ADC(b[1], c[1], *carrystart);
  c[2] = ADD(a[2], b[2], *carrystart);
  *carrystart = ADC(b[2], c[2], *carrystart);
  c[3] = ADD(a[3], b[3], *carrystart);
  *carrystart = ADC(b[3], c[3], *carrystart);//for addition, we need this flag to be set correctly.
};
static void addition64_double
(const uint64_t * a,
 const uint64_t * b,
 uint64_t *c,
 int * carrystart){
  //stores a+b in c.
  //carry bit stored in "carry"
  //carry = *carrystart;
  c[0] = ADD(a[0], b[0], *carrystart);
  *carrystart = ADC(b[0], c[0], *carrystart);
  c[1] = ADD(a[1], b[1], *carrystart);
  *carrystart = ADC(b[1], c[1], *carrystart);
  c[2] = ADD(a[2], b[2], *carrystart);
  *carrystart = ADC(b[2], c[2], *carrystart);
  c[3] = ADD(a[3], b[3], *carrystart);
  *carrystart = ADC(b[3], c[3], *carrystart);
  c[4] = ADD(a[4], b[4], *carrystart);
  *carrystart = ADC(b[4], c[4], *carrystart);
  c[5] = ADD(a[5], b[5], *carrystart);
  *carrystart = ADC(b[5], c[5], *carrystart);
  c[6] = ADD(a[6], b[6], *carrystart);
  *carrystart = ADC(b[6], c[6], *carrystart);
  c[7] = ADD(a[7], b[7], *carrystart);
  *carrystart = ADC(b[7], c[7], *carrystart);
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
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //c = (a-b) mod ?q
  //int subcarry = 0;
  if(greater_than(a, b)){
    subtract64(a, b, c);//c=a-b
  } else {
    subtract64(q, b, c);//c=q-b
    int subcarry = 0;
    addition64(c, a, c, &subcarry);//c=c+a
  } 
}

static void add2
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //c = (a+b) mod ?q
  int addcarry = 0;
  //addition64(a, b, c, 0);//c = a+b;
  addition64(a, b, c, &addcarry);//c = a+b;
  if(addcarry || greater_than(c, q)){
    //addcarry = 0;
    subtract64(c, q, c);//c = c-q
  }
}

//uint64_t mulcarry;
static void multiply64
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

uint64_t x;
static void print32
(uint64_t * x)
{
  printf(" %lu %lu %lu %lu \n", x[0], x[1], x[2], x[3]);
}
static void print64
(uint64_t * x)
{
  printf(" %lu %lu %lu %lu %lu %lu %lu %lu \n", x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]);

}

static void redc2(uint64_t * r, uint64_t * c)
{
  uint64_t mulcarry = 0;
  uint64_t mulcarry2 = 0;
  uint64_t k;

  k = r[0] * INV;
  mac(r[0], k, q[0], 0, &c[0], &mulcarry);
  mac(r[1], k, q[1], mulcarry, &r[1], &mulcarry);
  mac(r[2], k, q[2], mulcarry, &r[2], &mulcarry);
  mac(r[3], k, q[3], mulcarry, &r[3], &mulcarry);
  r[4] = ADD(r[4], mulcarry, 0);
  mulcarry2 = ADC(mulcarry, r[4], mulcarry2);

  k = r[1] * INV;
  mac(r[1], k, q[0], 0, &c[0], &mulcarry);
  mac(r[2], k, q[1], mulcarry, &r[2], &mulcarry);
  mac(r[3], k, q[2], mulcarry, &r[3], &mulcarry);
  mac(r[4], k, q[3], mulcarry, &r[4], &mulcarry);
  r[5] = ADD(r[5], mulcarry, mulcarry2);
  mulcarry2 = ADC(mulcarry, r[5], mulcarry2);

  k = r[2] * INV;
  mac(r[2], k, q[0], 0, &c[0], &mulcarry);
  mac(r[3], k, q[1], mulcarry, &r[3], &mulcarry);
  mac(r[4], k, q[2], mulcarry, &r[4], &mulcarry);
  mac(r[5], k, q[3], mulcarry, &r[5], &mulcarry);
  r[6] = ADD(r[6], mulcarry, mulcarry2);
  mulcarry2 = ADC(mulcarry, r[6], mulcarry2);

  k = r[3] * INV;
  mac(r[3], k, q[0], 0, &c[0], &mulcarry);
  mac(r[4], k, q[1], mulcarry, &r[4], &mulcarry);
  mac(r[5], k, q[2], mulcarry, &r[5], &mulcarry);
  mac(r[6], k, q[3], mulcarry, &r[6], &mulcarry);
  r[7] = ADD(r[7], mulcarry, mulcarry2);

  uint64_t * tmq2 = &r[4];
  if(greater_than(tmq2, q)){
    subtract64(tmq2, q, c);
  } else {
    memcpy(c, tmq2, 32);//there is probably a way to do this with only sending pointers around.
  }
};

static void redc(uint64_t * t, uint64_t * c)
{
  uint64_t redc_tbiq[8];
  uint64_t redc_mq[8];
  uint64_t tmq[8];
  //this is montgomery reduction. c = t mod q
  //t is 512 bytes.

  //tb:256 = low(t)
  //m:256 = low(tb*iq)
  //t2 = high(t + m*q)

  //t2 >= q -> c = t2-q
  //true -> c = t2

  multiply64(t,(uint64_t *)iq, redc_tbiq);
  //redc_tbiq = low(t * iq);

  multiply64((uint64_t *)redc_tbiq,
             (uint64_t *)q, redc_mq);
  //redc_mq = low(low(t * iq) * q)

  int double_carry = 0;
  
  addition64_double
    (t, redc_mq, tmq, &double_carry);
  //carry = double_carry;
  //tmq = t + redc_mq

  //need the high 64 bits of tmq.
  uint64_t * tmq2 = &tmq[4];
  
  //if(double_carry || greater_than(tmq2, q)){
  if(greater_than(tmq2, q)){
    //printf("greater than\n");
    //print32(&tmq[4]);
    //print32(q);
    subtract64(tmq2, q, c);
  } else {
    //printf("less than\n");
    memcpy(c, tmq2, 32);//there is probably a way to do this with only sending pointers around.
  }
}

//uint64_t mul2_r[8];
static void mul2
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //c = (a*b) mod ?q
  //costs around 3 multiplications of 256 bit numbres.

  uint64_t mul2_r[8];
  multiply64(a, b, mul2_r);
  redc2(mul2_r, c);
}

//uint64_t C[4];
static ERL_NIF_TERM sub
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  enif_inspect_binary(env, argv[0], &BinA);//0.01
  enif_inspect_binary(env, argv[1], &BinB);//0.01

  uint64_t C[4];

  sub2((uint64_t *)BinA.data,
       (uint64_t *)BinB.data, C);//~0.007
  resultnif.data = (char *)C;

  //0.03 is left unexplained.
  
  return enif_make_binary(env, &resultnif);//0.0125
}

static ERL_NIF_TERM add
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  enif_inspect_binary(env, argv[0], &BinA);
  enif_inspect_binary(env, argv[1], &BinB);
  uint64_t C[4];

  add2((uint64_t *)BinA.data,
       (uint64_t *)BinB.data, C);//0.0163
  resultnif.data = (char *)C;

  return enif_make_binary(env, &resultnif);
}
static ERL_NIF_TERM mul
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  enif_inspect_binary(env, argv[0], &BinA);
  enif_inspect_binary(env, argv[1], &BinB);
  uint64_t C[4];

  mul2((uint64_t *)BinA.data,
              (uint64_t *)BinB.data,
       (uint64_t *)C);//0.058
  resultnif.data = (char *)C;

  return enif_make_binary(env, &resultnif);
}


static ErlNifFunc nif_funcs[] =
  {
   {"sub", 2, sub},
   {"add", 2, add},
   {"mul", 2, mul},
   {"setup", 1, setup}
  };

ERL_NIF_INIT(fq2,nif_funcs,NULL,NULL,NULL,NULL)
