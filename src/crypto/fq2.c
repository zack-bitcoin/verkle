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


//<<A:64, B:64, C:64, D:64>> = fq:encode(1).
//{D, C, B, A}.
const uint64_t one[4] =
{8589934590U,
 6378425256633387010U,
 11064306276430008309U,
 1739710354780652911U};
  
//{8000017657123382296U,
// 17676554788265757849U,
// 164384689140237400U,
// 18374686475393433600U};

//-(q^-1 mod 2^64) mod 2^64
//ffff_fffe_ffff_ffff
//FFFFFFFEFFFFFFFF
const uint64_t INV = 18446744069414584319U;
//18446744073441116159 other endian?

//uint64_t C[4];
//uint64_t arr[2];
//int carry;

//subtract borrow
#define SUB(A, B, car) (A - B - car)
//add carry
#define ADC(a, b, c, car) {c = a + b + car; car = ((c < b) || (car && (c == b)));}

#define ADC2(a, b, car, c, car2) {c = a + b + car; car2 = ((c < b) || (car && (c == b)));}

//uint64_t x;
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

static ERL_NIF_TERM setup
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  return(argv[0]);
}

static inline void neg2
(uint64_t * a)
{
  subtract64(q, a, a);
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
(uint64_t * a, uint32_t b)
{
  uint64_t acc[4];
  memcpy(acc, one, 32);
  while(b > 0){
    if((b % 2) == 1){
      mul2(acc, a, acc);
    }
    square2(a, a);
    b = b >> 1;
  };
  memcpy(a, acc, 32);
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
(uint64_t * a, uint64_t * b)
{
  
  uint64_t acc[4];
  //uint64_t c[4];
  memcpy(acc, one, 32);
  //memcpy(c, a, 32);
  pow3(a, b[0], acc);
  pow3(a, b[1], acc);
  pow3(a, b[2], acc);
  pow3(a, b[3], acc);

  memcpy(a, acc, 32);
  //memcpy(a, one, 32);
}

static inline void e_double2
(uint64_t * u, uint64_t * v, uint64_t * z,
 uint64_t * t1, uint64_t * t2)
{
  uint64_t uu[4];
  uint64_t vv[4];
  uint64_t z2[4];
  square2(u, uu);
  square2(v, vv);
  add2(z, z, z2);
  mul2(z2, z, z2);//zz2
  add2(u, v, u);//uv1
  mul2(u, u, u);//uv2

  add2(vv, uu, t2);//vv_plus_uu, completed v
  sub2(vv, uu, z);//vv_minus_uu, completed z
  sub2(u, t2, t1);//completed u
  sub2(z2, z, uu);//completed t

  mul2(t1, uu, u);
  mul2(t2, z, v);
  mul2(z, uu, z);
};
static inline void e_add2
(uint64_t * u, uint64_t * v, uint64_t * z1,
 uint64_t * t1, uint64_t * t2,
 uint64_t * vpu2, uint64_t * vmu2,
 uint64_t * td2, uint64_t * z2)
{
  uint64_t vmu1[4];
  uint64_t vpu1[4];
  uint64_t a[4];
  uint64_t b[4];
  uint64_t td1[4];
  uint64_t c[4];
  uint64_t d[4];
  uint64_t zdup[4];

  sub2(v, u, vmu1);
  mul2(vmu1, vmu2, a);
  add2(v, u, vpu1);
  mul2(vpu1, vpu2, b);
  mul2(t1, t2, td1);
  mul2(td1, td2, c);
  add2(z1, z1, zdup);
  mul2(zdup, z2, d);

  sub2(b, a, t1);//completed u.
  add2(b, a, t2);//completed v.
  add2(d, c, z1);//completed z.
  sub2(d, c, a);//completed t

  mul2(t1, a, u);
  mul2(t2, z1, v);
  mul2(z1, a, z1);
}
/*
static void square_multi
(uint64_t * n, uint times)
{
  for(; times>0; times--){
    square2(n, n);
  };
};

static inline void inv2
(uint64_t * a, uint64_t * b)
{
  uint64_t t0[4];
  uint64_t t1[4];
  uint64_t t2[4];
  uint64_t t3[4];
  uint64_t t4[4];
  uint64_t t5[4];
  uint64_t t6[4];
  uint64_t t7[4];
  uint64_t t8[4];
  uint64_t t9[4];
  uint64_t t11[4];
  uint64_t t12[4];
  uint64_t t13[4];
  uint64_t t14[4];
  uint64_t t15[4];
  uint64_t t16[4];
  uint64_t t17[4];
  
  square2(a, t0);
  mul2(t0, a, t1);
  square2(t0, t16);
  square2(t16, t6);
  mul2(t6, t0, t5);
  mul2(t6, t16, t0);
  mul2(t5, t16, t12);
  square2(t6, t2);
  mul2(t5, t6, t7);
  mul2(t0, t5, t15);
  square2(t12, t17);
  mul2(t1, t17, t1);
  mul2(t7, t2, t3);
  mul2(t1, t17, t8);
  mul2(t8, t2, t4);
  mul2(t8, t7, t9);
  mul2(t4, t5, t7);
  mul2(t4, t17, t11);
  mul2(t9, t17, t5);
  mul2(t7, t15, t14);
  mul2(t11, t12, t13);
  mul2(t11, t17, t12);
  mul2(t15, t12, t15);
  mul2(t16, t15, t16);
  mul2(t3, t16, t3);
  mul2(t17, t3, t17);
  mul2(t0, t17, t0);
  mul2(t6, t0, t6);
  mul2(t2, t6, t2);

  square_multi(t0, 8);
  mul2(t0, t17, t0);
  square_multi(t0, 9);
  mul2(t0, t16, t0);
  square_multi(t0, 9);
  mul2(t0, t15, t0);
  square_multi(t0, 9);
  mul2(t0, t15, t0);
  square_multi(t0, 7);
  mul2(t0, t14, t0);
  square_multi(t0, 7);
  mul2(t0, t13, t0);
  square_multi(t0, 10);
  mul2(t0, t12, t0);
  square_multi(t0, 9);
  mul2(t0, t11, t0);
  square_multi(t0, 8);
  mul2(t0, t8, t0);
  square_multi(t0, 8);
  mul2(t0, a, t0);
  square_multi(t0, 14);
  mul2(t0, t9, t0);
  square_multi(t0, 10);
  mul2(t0, t8, t0);
  square_multi(t0, 15);
  mul2(t0, t7, t0);
  square_multi(t0, 10);
  mul2(t0, t6, t0);
  square_multi(t0, 8);
  mul2(t0, t5, t0);
  square_multi(t0, 16);
  mul2(t0, t3, t0);
  square_multi(t0, 8);
  mul2(t0, t2, t0);
  square_multi(t0, 7);
  mul2(t0, t4, t0);
  square_multi(t0, 9);
  mul2(t0, t2, t0);
  square_multi(t0, 8);
  mul2(t0, t3, t0);
  square_multi(t0, 8);
  mul2(t0, t2, t0);
  square_multi(t0, 8);
  mul2(t0, t2, t0);
  square_multi(t0, 8);
  mul2(t0, t2, t0);
  square_multi(t0, 8);
  mul2(t0, t3, t0);
  square_multi(t0, 8);
  mul2(t0, t2, t0);
  square_multi(t0, 8);
  mul2(t0, t2, t0);
  square_multi(t0, 5);
  mul2(t0, t1, t0);
  square_multi(t0, 5);
  mul2(t0, t1, b);
  
}
*/

static ERL_NIF_TERM neg
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary A;
  enif_inspect_binary(env, argv[0], &A);
  neg2((uint64_t *)A.data);
  return enif_make_binary(env, &A);
}
static ERL_NIF_TERM sub
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary BinAi;
  ErlNifBinary BinBi;
  enif_inspect_binary(env, argv[0], &BinAi);
  enif_inspect_binary(env, argv[1], &BinBi);
  uint64_t C[4];
  sub2((uint64_t *)BinAi.data,
       (uint64_t *)BinBi.data,
       C);//~0.007
  BinAi.data = (char *)C;
  enif_release_binary(&BinBi);
  return enif_make_binary(env, &BinAi);
}

static ERL_NIF_TERM add
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary BinAi;
  ErlNifBinary BinBi;
  enif_inspect_binary(env, argv[0], &BinAi);
  enif_inspect_binary(env, argv[1], &BinBi);
  add2((uint64_t *)BinAi.data,
       (uint64_t *)BinBi.data,
       (uint64_t *)BinAi.data);
  enif_release_binary(&BinBi);
  return enif_make_binary(env, &BinAi);
}
static ERL_NIF_TERM mul
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary BinAi;
  ErlNifBinary BinBi;
  enif_inspect_binary(env, argv[0], &BinAi);
  enif_inspect_binary(env, argv[1], &BinBi);
  mul2((uint64_t *)BinAi.data,
       (uint64_t *)BinBi.data,
       (uint64_t *)BinAi.data);
  enif_release_binary(&BinBi);
  return enif_make_binary(env, &BinAi);
};
static ERL_NIF_TERM square
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary BinAi;
  enif_inspect_binary(env, argv[0], &BinAi);
  square2((uint64_t *)BinAi.data,
          (uint64_t *)BinAi.data);
  return enif_make_binary(env, &BinAi);
};
static ERL_NIF_TERM power
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary A, B;
  enif_inspect_binary(env, argv[0], &A);
  enif_inspect_binary(env, argv[1], &B);
  pow2((uint64_t *)A.data,
       (uint64_t *)B.data);
  enif_release_binary(&B);
  return enif_make_binary(env, &A);
};
static ERL_NIF_TERM short_power
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary A;
  ErlNifUInt64 B;
  enif_inspect_binary(env, argv[0], &A);
  enif_get_uint64(env, argv[1], &B);
  short_pow2((uint64_t *)A.data,
             (uint32_t) B);
  //enif_release_binary(&B);
  return enif_make_binary(env, &A);
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
static ERL_NIF_TERM e_double
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary A;
  enif_inspect_binary(env, argv[0], &A);

  uint64_t * U = (uint64_t *)&A.data[0];
  uint64_t * V = (uint64_t *)&A.data[32];
  uint64_t * Z = (uint64_t *)&A.data[64];
  uint64_t * T1 = (uint64_t *)&A.data[96];
  uint64_t * T2 = (uint64_t *)&A.data[128];

  e_double2(U, V, Z, T1, T2);
  return enif_make_binary(env, &A);
}
static ERL_NIF_TERM e_add
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary Extended, ENiels;
  enif_inspect_binary(env, argv[0], &Extended);
  enif_inspect_binary(env, argv[1], &ENiels);

  uint64_t * U = (uint64_t *)&Extended.data[0];
  uint64_t * V = (uint64_t *)&Extended.data[32];
  uint64_t * Z = (uint64_t *)&Extended.data[64];
  uint64_t * T1 = (uint64_t *)&Extended.data[96];
  uint64_t * T2 = (uint64_t *)&Extended.data[128];

  uint64_t * VPU = (uint64_t *)&ENiels.data[0];
  uint64_t * VMU = (uint64_t *)&ENiels.data[32];
  uint64_t * T2D = (uint64_t *)&ENiels.data[64];
  uint64_t * NZ = (uint64_t *)&ENiels.data[96];

  e_add2(U, V, Z, T1, T2, VPU, VMU, T2D, NZ);

  return enif_make_binary(env, &Extended);
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
   //{"inv", 1, inv},

   {"e_double", 1, e_double},
   {"e_add", 2, e_add},

   {"ctest", 1, ctest},
   {"setup", 1, setup}
  };

ERL_NIF_INIT(fq2,nif_funcs,NULL,NULL,NULL,NULL)
