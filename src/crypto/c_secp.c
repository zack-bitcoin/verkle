#include <erl_nif.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

//finite field used to implement the secp256k1 elliptic curve.
//uses montgomery notation for fast multiplication.

//2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
//least significant part is first.



//<<A:64/little, B:64/little, C:64/little, D:64/little>> = <<Prime:256/little>>.
    //{A, B, C, D}.
const uint64_t q[4] =
  {
   18446744069414583343U,
   18446744073709551615U,
   18446744073709551615U,
   18446744073709551615U
  };

// inverse(2)
//unused
/*const uint64_t i2[4] =
  {
   18446744073709551607U,
   18446744073709551615U,
   18446744073709551615U,
   4611686018427387903U
   }; */
  /*  {4294967295U,
   12412584665171469313U,
   14755525175069779962U,
   869855177390326455U}; */

//<<A:64, B:64, C:64, D:64>> = fq:reverse_bytes(fq:encode(1)).
//encode(1) = mul(<<1:256/little>>, <<?r2:256/little>>).
// mul(A, B) = redc(A*B)
//{D, C, B, A}.
const uint64_t one[4] =
  {4294968273U,0U,0U,0U};
//{38U,
//0U,
//0U,
// 0U};

const uint64_t two[4] =
  {8589936546U,0U,0U,0U};

const uint64_t zero[4] =
  {0U,0U,0U,0U};

//16295367250680780974490674513165176452449235426866156013048779062215315747161
//unused
/*const uint64_t D2[4] =
{
 16993941304535871833U,
 63073048630374742U,
 1841551078520508720U,
 2596001775599221991U
 }; */

//{8000017657123382296U,
// 17676554788265757849U,
// 164384689140237400U,
// 18374686475393433600U};

//-(q^-1 mod 2^64) mod 2^64
//ffff_fffe_ffff_ffff
//FFFFFFFEFFFFFFFF
const uint64_t INV = //9708812670373448219U;
  15580212934572586289U;
//18446744069414584319U;
//18446744073441116159 other endian?

//uint64_t C[4];
//uint64_t arr[2];
//int carry;

//subtract borrow
#define SUB(A, B, car) (A - B - car)
//add carry
#define ADC(a, b, c, car) {c = a + b + car; car = ((c < b) || (car && (c == b)));}

#define ADC2(a, b, car, c, car2) {c = a + b + car; car2 = ((c < b) || (car && (c == b)));}

//#define kth_bit(n, k) ((n & ( 1 << k)) >> k)
#define kth_bit(n, k) ((n >> k) & 1)


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

static inline int is_zero(const uint64_t * M)
{
  return((M[0] == 0) &&
         (M[1] == 0) &&
         (M[2] == 0) &&
         (M[3] == 0));
};
static inline void neg2
(uint64_t * a, uint64_t * c)
{
  if(is_zero(a)) {
    memcpy(c, a, 32);
  } else {
    subtract64(q, a, c);
  }
};

static inline void sub2
(const uint64_t * a, const uint64_t * b,
 uint64_t * c)
{
  // dont do sub2(a, b, a). it doesn't work.
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
(const uint64_t * a, const uint64_t * b,
 uint64_t * c)
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
(const uint64_t * a, const uint64_t * b,
 uint64_t * c)
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
(const uint64_t * a, uint64_t * b)
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
(const uint64_t * a, const uint64_t * b,
 uint64_t * c)
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
  uint64_t A[4];
  memcpy(A, a, 32);
  while(b > 0){
    if((b % 2) == 1){
      mul2(c, A, c);
    }
    square2(A, A);
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

static inline void e_double2
(const uint64_t * x1, const uint64_t * y1,
 const uint64_t * z1, 
 uint64_t * x2, uint64_t * y2, uint64_t * z2)
{
  //http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
  /*
      A = X1^2
      B = Y1^2
      C = B^2
      D = 2*((X1+B)^2-A-C)
      E = 3*A
      F = E^2
      X3 = F-2*D
      Y3 = E*(D-X3)-8*C
      Z3 = 2*Y1*Z1

   */
  uint64_t a[4];
  uint64_t b[4];
  uint64_t c[4];
  uint64_t d[4];
  uint64_t e[4];
  uint64_t f[4];
  uint64_t g[4];
  uint64_t h[4];
  uint64_t i[4];

  square2(x1, a);//a
  square2(y1, b);//b
  square2(b, c);//c
  add2(x1, b, d);
  square2(d, e);
  sub2(e, a, d);
  sub2(d, c, e);
  add2(e, e, d);//d
  add2(a, a, f);
  add2(a, f, e);//e
  square2(e, f);//f;
  add2(d, d, y2);
  sub2(f, y2, x2);//x2

  add2(c, c, g);
  add2(g, g, c);
  add2(c, c, g);
  //mul2(c, 8, g);
  
  sub2(d, x2, h);
  mul2(e, h, i);
  sub2(i, g, y2);//y2
  add2(y1, y1, g);
  mul2(g, z1, z2);//z2
};

static inline int is_eq(const uint64_t * A,
                        const uint64_t * B)
{
  return((A[0] == B[0]) &&
         (A[1] == B[1]) &&
         (A[2] == B[2]) &&
         (A[3] == B[3]));
};
static inline int is_zero_point
(const uint64_t * X, const uint64_t * Y,
 const uint64_t * Z)
{
  return(is_zero(X) && is_eq(Y, Z));
};


static inline void e_add3
(const uint64_t * x1, const uint64_t * y1,
 const uint64_t * z1,
 const uint64_t * x2, const uint64_t * y2,
 uint64_t * x3, uint64_t * y3, uint64_t * z3)
{

//fast addition with Z2 = 1
//http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
/*
        Z1Z1 = Z1^2
      U2 = X2*Z1Z1
      S2 = Y2*Z1*Z1Z1
      H = U2-X1
      HH = H^2
      I = 4*HH
      J = H*I
      r = 2*(S2-Y1)
      V = X1*I
      X3 = r^2-J-2*V
      Y3 = r*(V-X3)-2*Y1*J
      Z3 = (Z1+H)^2-Z1Z1-HH

 */
  uint64_t Z1Z1[4];
  uint64_t U2[4];
  uint64_t S2[4];
  uint64_t H[4];
  uint64_t HH[4];
  uint64_t I[4];
  uint64_t J[4];
  uint64_t r[4];
  uint64_t V[4];
  uint64_t a[4];
  uint64_t b[4];
  uint64_t c[4];

  square2(z1, Z1Z1);
  mul2(x2, Z1Z1, U2);
  mul2(Z1Z1, z1, a);
  mul2(y2, a, S2);
  sub2(U2, x1, H);
  sub2(S2, y1, a);
  add2(a, a, r);

  if(is_zero(H)){
    if(is_zero(r)){
  //if h==0 and r==0, it is the same point twice. we should use the double algorithm.
      e_double2(x1, y1, z1, x3, y3, z3);
    } else {
  //if h==0, then they are additive inverses. we should return the zero point.
      memcpy(x3, zero, 32);
      memcpy(y3, one, 32);
      memcpy(z3, zero, 32);
    }
  } else {

  square2(H, HH);
  add2(HH, HH, a);
  add2(a, a, I);
  mul2(H, I, J);

  mul2(x1, I, V);
  square2(r, a);
  sub2(a, J, b);
  add2(V, V, a);
  sub2(b, a, x3);
  add2(y1, y1, a);
  mul2(a, J, b);
  sub2(V, x3, a);
  mul2(a, r, c);
  sub2(c, b, y3);
  add2(z1, H, a);
  square2(a, b);
  sub2(b, Z1Z1, a);
  sub2(a, HH, z3);
  }
};

static inline void e_add2
(const uint64_t * x1, const uint64_t * y1,
 const uint64_t * z1,
 const uint64_t * x2, const uint64_t * y2,
 const uint64_t * z2, 
 uint64_t * x3, uint64_t * y3, uint64_t * z3)
{
  //general addition secp256k1
  //http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
  /*
      Z1Z1 = Z1^2
      Z2Z2 = Z2^2
      U1 = X1*Z2Z2
      U2 = X2*Z1Z1
      S1 = Y1*Z2*Z2Z2
      S2 = Y2*Z1*Z1Z1
      H = U2-U1
      I = (2*H)^2
      J = H*I
      r = 2*(S2-S1)
      V = U1*I
      X3 = r^2-J-2*V
      Y3 = r*(V-X3)-2*S1*J
      Z3 = ((Z1+Z2)^2-Z1Z1-Z2Z2)*H
   */

  uint64_t Z1Z1[4];
  uint64_t Z2Z2[4];
  uint64_t U1[4];
  uint64_t U2[4];
  uint64_t S1[4];
  uint64_t S2[4];
  uint64_t H[4];
  uint64_t I[4];
  uint64_t J[4];
  uint64_t r[4];
  uint64_t V[4];
  uint64_t a[4];
  uint64_t b[4];
  uint64_t c[4];

  square2(z1, Z1Z1);
  square2(z2, Z2Z2);
  mul2(x1, Z2Z2, U1);
  mul2(x2, Z1Z1, U2);
  mul2(z2, Z2Z2, a);
  mul2(y1, a, S1);
  mul2(z1, Z1Z1, a);
  mul2(y2, a, S2);
  sub2(U2, U1, H);
  sub2(S2, S1, a);
  add2(a, a, r);

  if(is_zero(H)){
    if(is_zero(r)){
  //if h==0 and r==0, it is the same point twice. we should use the double algorithm.
      e_double2(x1, y1, z1, x3, y3, z3);
    } else {
  //if h==0, then they are additive inverses. we should return the zero point.
      memcpy(x3, zero, 32);
      memcpy(y3, one, 32);
      memcpy(z3, zero, 32);
    }
  } else {

    add2(H, H, a);
    square2(a, I);
    mul2(H, I, J);
    
    mul2(U1, I, V);
    square2(r, a);
    sub2(a, J, b);
    add2(V, V, a);
    sub2(b, a, x3);
    sub2(V, x3, a);
    mul2(r, a, b);
    mul2(S1, J, a);
    add2(a, a, c);
    sub2(b, c, y3);
    add2(z1, z2, a);
    square2(a, b);
    sub2(b, Z1Z1, a);
    sub2(a, Z2Z2, b);
    mul2(b, H, z3);
  }
};

static inline void e_mul_long2
(uint64_t * x, uint64_t * y,//point
 uint64_t * z, 
 uint64_t * b,//exponent
 uint64_t * x2, uint64_t * y2, //resulting point.
 uint64_t * z2)
{
  memcpy(x2, zero, 32);
  memcpy(y2, one, 32);
  memcpy(z2, zero, 32);
  //printf("\n");
  for(int i = 3; i >= 0; i--){
    //printf("\n");
    for(int j = 63; j >= 0; j--){
      int bool = kth_bit(b[i], j);
      e_double2(x2, y2, z2,
                x2, y2, z2);
      if(bool){
        e_add3(x2, y2, z2,
               x, y, 
               x2, y2, z2);
          //printf("a");
      } else {
          //printf(".");
      }
    }
  }
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
  ErlNifBinary A;
  int checka =
    enif_inspect_binary(env, argv[0], &A);
  if((!checka) || (!(A.size == 32))){
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
static ERL_NIF_TERM e_mul
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary Point;
  ErlNifUInt64 B;

  ERL_NIF_TERM Extended2;
  char * C = enif_make_new_binary
    (env, 128, &Extended2);
  
  int checka =
    enif_inspect_binary(env, argv[0], &Point);
  int checkb =
    enif_get_uint64(env, argv[1], &B);
  if((!checka) || (!(Point.size == 128))){
    return(error_atom(env));
  };
  if((!checkb)){
    return(error_atom(env));
  };
  
  uint64_t * X = (uint64_t *)&(Point.data[0]);
  uint64_t * Y = (uint64_t *)&(Point.data[32]);
  uint64_t * Z = (uint64_t *)&(Point.data[64]);
  uint64_t * T = (uint64_t *)&(Point.data[96]);

  uint64_t * X2 = (uint64_t *)&(C[0]);
  uint64_t * Y2 = (uint64_t *)&(C[32]);
  uint64_t * Z2 = (uint64_t *)&(C[64]);
  uint64_t * T2 = (uint64_t *)&(C[96]);

  e_mul2(X, Y, Z, T,
         (uint64_t) B,
         X2, Y2, Z2, T2);
  enif_release_binary(&Point);

  return Extended2;
};
*/
static ERL_NIF_TERM e_mul_long
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary Point, B;

  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 96, &Result);
  
  int checka =
    enif_inspect_binary(env, argv[0], &Point);
  int checkb =
    enif_inspect_binary(env, argv[1], &B);
  if((!checka)){
    //printf("mul error elliptic point\n");
    return(error_atom(env));
  };
  if((!(Point.size == 96))){
    //printf("mul error elliptic point size\n");
    return(error_atom(env));
  }
  if((!checkb) || (!(B.size == 32))){
    //printf("mul error exponent size\n");
    return(error_atom(env));
  };
  uint64_t * X2 = (uint64_t *)&(C[0]);
  uint64_t * Y2 = (uint64_t *)&(C[32]);
  uint64_t * Z2 = (uint64_t *)&(C[64]);

  uint64_t * X = (uint64_t *)&(Point.data[0]);
  uint64_t * Y = (uint64_t *)&(Point.data[32]);
  uint64_t * Z = (uint64_t *)&(Point.data[64]);
  if(!(Point.data[64] == 1U)){
    printf("unsimplified e_mul error\n");
    return(error_atom(env));
  };

  if((B.data[0] == 0U) &&
     (B.data[32] == 0U) &&
     (B.data[64] == 0U)){
    // printf("exponent is zero in e_mul\n");
    memcpy(X2, zero, 32);
    memcpy(Y2, one, 32);
    memcpy(Z2, zero, 32);
  } else if(is_zero_point(X, Y, Z)) {
    //printf("elliptic point is zero\n");
    memcpy(X2, zero, 32);
    memcpy(Y2, one, 32);
    memcpy(Z2, zero, 32);
  } else {
    e_mul_long2(X, Y, Z,
                (uint64_t *)B.data,
                X2, Y2, Z2);
  }
  enif_release_binary(&Point);
  enif_release_binary(&B);
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
static ERL_NIF_TERM e_double
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary A;
  int checka =
    enif_inspect_binary(env, argv[0], &A);
  if((!checka) || (!(A.size == 96))){
    return(error_atom(env));
  };

  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 96, &Result);

  uint64_t * U = (uint64_t *)&A.data[0];
  uint64_t * V = (uint64_t *)&A.data[32];
  uint64_t * Z = (uint64_t *)&A.data[64];

  uint64_t * Ub = (uint64_t *)&(C[0]);
  uint64_t * Vb = (uint64_t *)&(C[32]);
  uint64_t * Zb = (uint64_t *)&(C[64]);

  //if(is_zero_point(U, V, Z)){
  //  memcpy(Ub, zero, 32);
  //  memcpy(Vb, one, 32);
  //  memcpy(Zb, one, 32);
  //  memcpy(Tb, zero, 32);
  //} else {

  e_double2(U, V, Z, Ub, Vb, Zb);
  //}
  //  return enif_make_binary(env, &A);
  enif_release_binary(&A);
  return(Result);
}
static ERL_NIF_TERM e_add
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary Extended, ENiels;
  int checka =
    enif_inspect_binary(env, argv[0], &Extended);
  int checkb =
    enif_inspect_binary(env, argv[1], &ENiels);
  if((!checka) || (!(Extended.size == 96))){
    return(error_atom(env));
  };
  if((!checkb) || (!(ENiels.size == 96))){
    return(error_atom(env));
  };
  
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 96, &Result);

  uint64_t * X1 = (uint64_t *)&Extended.data[0];
  uint64_t * Y1 = (uint64_t *)&Extended.data[32];
  uint64_t * Z1 = (uint64_t *)&Extended.data[64];

  uint64_t * X2 = (uint64_t *)&ENiels.data[0];
  uint64_t * Y2 = (uint64_t *)&ENiels.data[32];
  uint64_t * Z2 = (uint64_t *)&ENiels.data[64];

  uint64_t * X3 = (uint64_t *)&(C[0]);
  uint64_t * Y3 = (uint64_t *)&(C[32]);
  uint64_t * Z3 = (uint64_t *)&(C[64]);

  /*
  if(is_zero_point(X1, Y1, Z1)){
    memcpy(X3, X2, 32);
    memcpy(Y3, Y2, 32);
    memcpy(Z3, Z2, 32);
  } else if(is_zero_point(X2, Y2, Z2)){
    memcpy(X3, X1, 32);
    memcpy(Y3, Y1, 32);
    memcpy(Z3, Z1, 32);
  } else {
    */
    e_add2(X1, Y1, Z1,
           X2, Y2, Z2,
           X3, Y3, Z3);
    //}
  enif_release_binary(&ENiels);
  enif_release_binary(&Extended);
  return(Result);
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

   {"double", 1, e_double},
   {"padd", 2, e_add},
   //{"pmul", 2, e_mul},
   {"pmul_long", 2, e_mul_long}

   //{"ctest", 1, ctest}
  };

ERL_NIF_INIT(c_secp,nif_funcs,NULL,NULL,NULL,NULL)
