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

uint64_t C[4];
uint64_t arr[2];
int carry;

//add carry
#define ADD(A, B) (A + B + carry)
//the carry bit.
#define ADC(B, C) ((C<B) ||(carry && (C == B)))

//subtract borrow
#define SUB(A, B) (A - B - carry)

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

static void mac
(const uint64_t a, const uint64_t b,
 const uint64_t c, const uint64_t mac_carry,
 uint64_t * result, uint64_t * next_carry) {
  //a + (b * c) + carry
  __uint128_t prod =
    (__uint128_t)a + ((__uint128_t)b * (__uint128_t)c) + (__uint128_t)mac_carry;
  *result = prod;
  *next_carry = prod >> 64;
}

int nextcarry;
static void subtract64
(const uint64_t * a,
 const uint64_t * b,
 uint64_t * c){
  //stores a-b in c, borrow bit in "carry"
  carry = 0;
  nextcarry = (a[0] < b[0]);
  c[0] = SUB(a[0], b[0]);
  carry = nextcarry;
  nextcarry = (a[1] < b[1]);
  c[1] = SUB(a[1], b[1]);
  carry = nextcarry;
  nextcarry = (a[2] < b[2]);
  c[2] = SUB(a[2], b[2]);
  carry = nextcarry;
  nextcarry = (a[3] < b[3]);
  c[3] = SUB(a[3], b[3]);
};
static void addition64
(const uint64_t * a,
 const uint64_t * b,
 uint64_t *c,
 int carrystart){
  //stores a+b in c.
  //carry bit stored in "carry"
  carry = carrystart;
  c[0] = ADD(a[0], b[0]);
  carry = ADC(b[0], c[0]);
  c[1] = ADD(a[1], b[1]);
  carry = ADC(b[1], c[1]);
  c[2] = ADD(a[2], b[2]);
  carry = ADC(b[2], c[2]);
  c[3] = ADD(a[3], b[3]);
  carry = ADC(b[3], c[3]);//for addition, we need this flag to be set correctly.
};
static void addition64_double
(const uint64_t * a,
 const uint64_t * b,
 uint64_t *c,
 int carrystart){
  //stores a+b in c.
  //carry bit stored in "carry"
  carry = carrystart;
  c[0] = ADD(a[0], b[0]);
  carry = ADC(b[0], c[0]);
  c[1] = ADD(a[1], b[1]);
  carry = ADC(b[1], c[1]);
  c[2] = ADD(a[2], b[2]);
  carry = ADC(b[2], c[2]);
  c[3] = ADD(a[3], b[3]);
  carry = ADC(b[3], c[3]);
  c[4] = ADD(a[4], b[4]);
  carry = ADC(b[4], c[4]);
  c[5] = ADD(a[5], b[5]);
  carry = ADC(b[5], c[5]);
  c[6] = ADD(a[6], b[6]);
  carry = ADC(b[6], c[6]);
  c[7] = ADD(a[7], b[7]);
  carry = ADC(b[7], c[7]);
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
  if(greater_than(a, b)){
    subtract64(a, b, c);//c=a-b
  } else {
    subtract64(q, b, c);//c=q-b
    addition64(c, a, c, 0);//c=c+a
  } 
}

static void add2
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //c = (a+b) mod ?q
  addition64(a, b, c, 0);//c = a+b;
  if(carry || greater_than(c, q)){
    subtract64(c, q, c);//c = c-q
  }
}

uint64_t mulcarry;
static void multiply64
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //a is 256 bits, b is 256 bits, c is 512 bits.
  //c = a * b.
  mulcarry = 0;
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

uint64_t r[17];
uint carries[16];//an extra slot at the end so we can do for loops without needing a special case for the last iteration.
uint64_t r3[8];
int mul_carry;
uint64_t x;
uint64_t low;
uint64_t high;
uint64_t highlow;
int ij;
uint64_t thiscarry;
int hi;
int64_t slider;
uint64_t x;

static void multiply32
(uint32_t * a, uint32_t * b, uint64_t * r2)
{
  //a and b are 256 bits. r2 is 512 bits.
  // r2 = a*b;

  //costs around 64, 64-bit multiplications and 256, 64-bit additions.

  //least significant is in [0]th position.
  uint64_t r[17] = { 0 };
  uint carries[16] = { 0 };
  carry = 0;
  for(int i = 0; i<8; i++) {
    for(int j = 0; j<8; j++) {
      x = (uint64_t)a[i] * (uint64_t)b[j];
      ij = i + j;
      r[ij] = ADD(r[ij], x);
      carries[ij] += ADC(x, r[ij]);
    }
  }
  //printf("x is %lu %u \n", x, a[0]);
  /*
    1111
      1111
        1111
   */

  //(uint64_t *)c;
  high = 0;
  low = r[1] >> 32;
  r2[0] = ADD(r[0], low);
  carries[1] += ADC(low, r2[0]);
  thiscarry = carries[0];
  thiscarry = thiscarry >> 32;
  r2[0] = ADD(r2[0], thiscarry);
  carries[1] += ADC(thiscarry, r2[0]);
  for(int i = 2; i < 16; i += 2){
    hi = i>>1;
    high = r[i-1] << 32;
    low = r[i+1] >> 32;
    highlow = high + low;
    r2[hi] = ADD(r[i], highlow);
    carries[i+1] += ADC(high, r2[hi]);
    thiscarry = carries[i];
    thiscarry = thiscarry >> 32;
    thiscarry += carries[i-1];
    r2[hi] = ADD(r2[0], thiscarry);
    carries[i+1] += ADC(thiscarry, r2[hi]);
  }

};
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


//%R and N need to be coprime.
//%IN * N rem R needs to be -1.
uint64_t redc_tb[4];
uint64_t redc_m[4];
uint64_t redc_t2[4];
uint64_t redc_tbiq[8];
uint64_t redc_mq[8];
uint64_t tmq[8];
uint redc_carry;
static void redc(uint64_t * t, uint64_t * c)
{
  //this is montgomery reduction. c = t mod q
  //t is 512 bytes.

  //define iq like this: q*iq = -1 mod 2^256

  //tb:256 = low(t)
  //m:256 = low(tb*iq)
  //t2 = high(t + m*q)

  //t2 >= q -> c = t2-q
  //true -> c = t2
  //printf(" t %lu %lu %lu %lu \n", t[0], t[1], t[2], t[3]);

  memcpy(redc_tb, t, 32);
  multiply64((uint64_t *)redc_tb,
             (uint64_t *)iq, redc_tbiq);
  memcpy(redc_m, redc_tbiq, 32);
  multiply64((uint64_t *)redc_m,
             (uint64_t *)q, redc_mq);
  addition64_double(t, redc_mq, tmq, 0);

  //need the high half of tmq.
  uint64_t * tmq2 = &tmq[4];
  
  if(greater_than(tmq2, q)){
    subtract64(tmq2, q, c);
  } else {
    memcpy(c, tmq2, 32);
    //c = tmq2;
    //c = tmq2;
  }
}



static void mul2
(uint64_t * a, uint64_t * b, uint64_t * c)
{
  //c = (a*b) mod ?q
  //costs around 3 multiplications of 256 bit numbres.
  /*
  uint64_t x, y;
  mac(5, 1844674407370955161U,184467400U,
      3, &x, &y);
  printf("x: %lu y: %lu \n", x, y);
  */

  uint64_t r[8];
  multiply64(a, b, r);
  //print64(r);

  //multiply32(a, b, r3);
  //print64(r3);
  //c[3] = r3[3];
  redc(r, c);
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
static ERL_NIF_TERM mul
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  enif_inspect_binary(env, argv[0], &BinA);
  enif_inspect_binary(env, argv[1], &BinB);

  mul2((uint64_t *)BinA.data,
              (uint64_t *)BinB.data,
       (uint64_t *)C);
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
