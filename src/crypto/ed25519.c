#include <erl_nif.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

//finite field for prime 2^255 - 19. Used to implement Ed25519 elliptic curve.
//uses montgomery notation for fast multiplication.

//2^255 - 19
//least significant part is first.
const uint64_t q[4] =
  {
   18446744073709551597U,
   18446744073709551615U,
   18446744073709551615U,
   9223372036854775807U,
  };

// inverse(2)
const uint64_t i2[4] =
  {
   18446744073709551607U,
   18446744073709551615U,
   18446744073709551615U,
   4611686018427387903U
  };
  /*  {4294967295U,
   12412584665171469313U,
   14755525175069779962U,
   869855177390326455U}; */


//<<A:64, B:64, C:64, D:64>> = fq:reverse_bytes(fq:encode(1)).
//encode(1) = mul(<<1:256/little>>, <<?r2:256/little>>).
// mul(A, B) = redc(A*B)
//{D, C, B, A}.
const uint64_t one[4] =
{38U,
0U,
0U,
 0U};

const uint64_t two[4] =
{76U,
0U,
0U,
 0U};

const uint64_t zero[4] =
  {0U,0U,0U,0U};

//16295367250680780974490674513165176452449235426866156013048779062215315747161
const uint64_t D2[4] =
{
 16993941304535871833U,
 63073048630374742U,
 1841551078520508720U,
 2596001775599221991U
};

//{8000017657123382296U,
// 17676554788265757849U,
// 164384689140237400U,
// 18374686475393433600U};

//-(q^-1 mod 2^64) mod 2^64
//ffff_fffe_ffff_ffff
//FFFFFFFEFFFFFFFF
const uint64_t INV = 9708812670373448219U;
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

static inline void neg2
(uint64_t * a, uint64_t * c)
{
  subtract64(q, a, c);
};

static inline void sub2
(const uint64_t * a, const uint64_t * b,
 uint64_t * c)
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
(const uint64_t * x, const uint64_t * y,
 const uint64_t * z, const uint64_t * t,
 uint64_t * xb, uint64_t * yb, uint64_t * zb,
 uint64_t * tb)
{
  //todo. working here.
  uint64_t A[4];
  uint64_t B[4];
  uint64_t ZZ[4];
  uint64_t C[4];
  uint64_t D[4];
  uint64_t XY[4];
  uint64_t AB[4];
  uint64_t XYXY[4];
  uint64_t E[4];
  uint64_t G[4];
  uint64_t F[4];
  uint64_t H[4];

  square2(x, A);
  square2(y, B);
  square2(z, ZZ);
  mul2(two, ZZ, C);
  neg2(A, D);
  add2(x, y, XY);
  square2(XY, XYXY);
  add2(A, B, AB);
  sub2(XYXY, AB, E);
  add2(D, B, G);
  sub2(G, C, F);
  sub2(D, B, H);

  mul2(E, F, xb);
  mul2(G, H, yb);
  mul2(E, H, tb);
  mul2(F, G, zb);

  /*
  uint64_t uu[4];
  uint64_t vv[4];
  uint64_t z2[4];
  square2(u, uu);
  square2(v, vv);
  add2(z, z, z2);
  mul2(z2, z, z2);//zz2
  add2(u, v, ub);//uv1
  mul2(ub, ub, ub);//uv2

  add2(vv, uu, t2b);//vv_plus_uu, completed v
  sub2(vv, uu, zb);//vv_minus_uu, completed z
  sub2(ub, t2b, t1b);//completed u
  sub2(z2, zb, uu);//completed t

  mul2(t1b, uu, ub);
  mul2(t2b, zb, vb);
  mul2(zb, uu, zb);
  */
};
static inline void e_add2
(const uint64_t * x1, const uint64_t * y1,
 const uint64_t * z1,const uint64_t * t1,
 const uint64_t * x2, const uint64_t * y2,
 const uint64_t * z2, const uint64_t * t2,
 uint64_t * x3, uint64_t * y3, uint64_t * z3,
 uint64_t * t3)
{
  uint64_t k[4];
  uint64_t m[4];

  uint64_t a[4];
  uint64_t b[4];
  uint64_t f[4];
  uint64_t c[4];
  uint64_t d[4];
  uint64_t e[4];
  uint64_t g[4];
  uint64_t h[4];
  uint64_t tb[4];
  uint64_t zb[4];

  sub2(y1, x1, k);
  add2(y2, x2, m);
  mul2(k, m, a);

  add2(y1, x1, k);
  sub2(y2, x2, m);
  mul2(k, m, b);

  sub2(b, a, f);
  
  if(f == 0){
    e_double2(x1, y1, z1, t1,
              x3, y3, z3, t3);
  } else {
    add2(t2, t2, tb);
    //mul2(two, t2, tb);
    mul2(z1, tb, c);
    add2(z2, z2, zb);
    //mul2(two, z2, zb);
    mul2(t1, zb, d);
    add2(d, c, e);
    add2(b, a, g);
    sub2(d, c, h);
    mul2(e, f, x3);
    mul2(g, h, y3);
    mul2(e, h, t3);
    mul2(f, g, z3);
  }
  /*
  uint64_t a[4];
  uint64_t b[4];
  uint64_t c[4];
  uint64_t d[4];

  sub2(v, u, a);
  mul2(a, vmu2, a);
  add2(v, u, b);
  mul2(b, vpu2, b);
  mul2(t1, t2, c);
  mul2(c, td2, c);
  add2(z1, z1, d);
  mul2(d, z2, d);

  sub2(b, a, t1b);//completed u.
  add2(b, a, t2b);//completed v.
  add2(d, c, z1b);//completed z.
  sub2(d, c, a);//completed t

  mul2(t1b, a, ub);
  mul2(t2b, z1b, vb);
  mul2(z1b, a, z1b);
  */
};
static inline void extended2extended_niels
(
 //extended point
 uint64_t * u, uint64_t * v, uint64_t * z1,
 uint64_t * t1, uint64_t * t2,
 //resulting niels points
 uint64_t * vpu, uint64_t * vmu,
 uint64_t * td, uint64_t * z2
 )
{
  mul2(t1, t2, td);
  mul2(td, D2, td);
  add2(u, v, vpu);
  sub2(v, u, vmu);
  memcpy(z2, z1, 32);
};
static inline void extended_niels2extended
(uint64_t * vpu, uint64_t * vmu,//niels points
 uint64_t * td, uint64_t * z2,
 uint64_t * u, uint64_t * v, uint64_t * z1,//resulting extended point.
 uint64_t * t1, uint64_t * t2)
{
  //{u = 0, v = 1, z = 1, t1 = 0, t2 = 0},
  /*  e_add2(zero, one, one, zero, zero,//zero point
         vpu, vmu, td, z2,
         u, v, z1, t1, t2);*/
};
static inline void e_mul2
(uint64_t * vpu, uint64_t * vmu,//niels points
 uint64_t * td, uint64_t * z2,
 uint64_t b,//exponent
 uint64_t * u, uint64_t * v, uint64_t * z1,//resulting extended point.
 uint64_t * t1, uint64_t * t2)
{
  if(b == 1){
    extended_niels2extended
      (vpu, vmu, td, z2, u, v, z1, t1, t2);
    /*
    add2(vpu, vmu, v);
    sub2(vpu, vmu, u);
    mul2(v, (uint64_t *)i2, v);
    mul2(u, (uint64_t *)i2, u);
    memcpy(z1, one, 32);
    memcpy(t1, u, 32);
    memcpy(t2, v, 32);
    */
  } else if((b % 2) == 0){
    e_mul2(vpu, vmu, td, z2,
           b / 2,
           u, v, z1, t1, t2);
    //e_double2(u, v, z1, t1, t2,
    //          u, v, z1, t1, t2);
    e_double2(u, v, z1, t1,
              u, v, z1, t1);
  } else {
    e_mul2(vpu, vmu, td, z2,
           b - 1,
           u, v, z1, t1, t2);
    /*    e_add2(u, v, z1, t1, t2,
           vpu, vmu, td, z2,
           u, v, z1, t1, t2);
    */
  };
};

static inline void e_mul_long2
(uint64_t * vpu, uint64_t * vmu,//niels points
 uint64_t * td, uint64_t * z2,
 uint64_t * b,//exponent
 uint64_t * u, uint64_t * v, uint64_t * z1,//resulting extended point.
 uint64_t * t1, uint64_t * t2)
{
  extended_niels2extended
    (vpu, vmu, td, z2, u, v, z1, t1, t2);
  int all_zero = 1;//true
  for(int i = 3; i >= 0; i--){
    for(int j = 63; j >= 0; j--){
      int bool = kth_bit(b[i], j);
      if(!(all_zero)){
        //e_double2(u, v, z1, t1, t2,
        //          u, v, z1, t1, t2);
        e_double2(u, v, z1, t1,
                  u, v, z1, t1);
        if(bool){
          /*
          e_add2(u, v, z1, t1, t2,
                 vpu, vmu, td, z2,
                 u, v, z1, t1, t2);
          */
        }
      }
      all_zero = (all_zero && (!(bool)));
    }
  }
}
    // 1 0 1
    // double, add, double, double, add
  

/*
  if(b == 1){
    //extended_niels2extended
    add2(vpu, vmu, v);
    sub2(vpu, vmu, u);
    mul2(v, (uint64_t *)i2, v);
    mul2(u, (uint64_t *)i2, u);
    memcpy(z1, one, 32);
    memcpy(t1, u, 32);
    memcpy(t2, v, 32);
  } else if((b % 2) == 0){
    e_mul2(vpu, vmu, td, z2,
           b / 2,
           u, v, z1, t1, t2);
    e_double2(u, v, z1, t1, t2,
              u, v, z1, t1, t2);
  } else {
    e_mul2(vpu, vmu, td, z2,
           b - 1,
           u, v, z1, t1, t2);
    e_add2(u, v, z1, t1, t2,
           vpu, vmu, td, z2,
           u, v, z1, t1, t2);
  };
};
*/
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
static ERL_NIF_TERM e_mul
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary ENiels;
  ErlNifUInt64 B;

  ERL_NIF_TERM Extended2;
  char * C = enif_make_new_binary
    (env, 160, &Extended2);
  
  int checka =
    enif_inspect_binary(env, argv[0], &ENiels);
  int checkb =
    enif_get_uint64(env, argv[1], &B);
  if((!checka) || (!(ENiels.size == 128))){
    return(error_atom(env));
  };
  if((!checkb)){
    return(error_atom(env));
  };
  
  uint64_t * VPU = (uint64_t *)&(ENiels.data[0]);
  uint64_t * VMU = (uint64_t *)&(ENiels.data[32]);
  uint64_t * T2D = (uint64_t *)&(ENiels.data[64]);
  uint64_t * NZ = (uint64_t *)&(ENiels.data[96]);

  uint64_t * U = (uint64_t *)&(C[0]);
  uint64_t * V = (uint64_t *)&(C[32]);
  uint64_t * Z = (uint64_t *)&(C[64]);
  uint64_t * T1 = (uint64_t *)&(C[96]);
  uint64_t * T2 = (uint64_t *)&(C[128]);

  e_mul2(VPU, VMU, T2D, NZ,
         (uint64_t) B,
         U, V, Z, T1, T2);
  enif_release_binary(&ENiels);

  return Extended2;
};
static ERL_NIF_TERM e_mul_long
(ErlNifEnv* env, int argc,
 const ERL_NIF_TERM argv[])
{
  ErlNifBinary ENiels, B;

  ERL_NIF_TERM Extended2;
  char * C = enif_make_new_binary
    (env, 160, &Extended2);
  
  int checka =
    enif_inspect_binary(env, argv[0], &ENiels);
  int checkb =
    enif_inspect_binary(env, argv[1], &B);
  if((!checka)){
    return(error_atom(env));
  };
  if((!(ENiels.size == 160)) &&
     (!(ENiels.size == 128))){
    return(error_atom(env));
  }
  if((!checkb) || (!(B.size == 32))){
    return(error_atom(env));
  };
  uint64_t * U = (uint64_t *)&(C[0]);
  uint64_t * V = (uint64_t *)&(C[32]);
  uint64_t * Z = (uint64_t *)&(C[64]);
  uint64_t * T1 = (uint64_t *)&(C[96]);
  uint64_t * T2 = (uint64_t *)&(C[128]);

  if(ENiels.size == 160){
    uint64_t * Ua = (uint64_t *)&ENiels.data[0];
    uint64_t * Va = (uint64_t *)&ENiels.data[32];
    uint64_t * Z1a = (uint64_t *)&ENiels.data[64];
    uint64_t * T1a = (uint64_t *)&ENiels.data[96];
    uint64_t * T2a = (uint64_t *)&ENiels.data[128];
    uint64_t VPU[4];
    uint64_t VMU[4];
    uint64_t T2D[4];
    uint64_t NZ[4];
    extended2extended_niels
      (
       Ua, Va, Z1a, T1a, T2a,
       VPU, VMU, T2D, NZ
       );
  e_mul_long2(VPU, VMU, T2D, NZ,
         (uint64_t *)B.data,
         U, V, Z, T1, T2);
  enif_release_binary(&ENiels);
  enif_release_binary(&B);
  return Extended2;
    
  } else if(ENiels.size == 128){
  uint64_t * VPU = (uint64_t *)&(ENiels.data[0]);
  uint64_t * VMU = (uint64_t *)&(ENiels.data[32]);
  uint64_t * T2D = (uint64_t *)&(ENiels.data[64]);
  uint64_t * NZ = (uint64_t *)&(ENiels.data[96]);

  e_mul_long2(VPU, VMU, T2D, NZ,
         (uint64_t *)B.data,
         U, V, Z, T1, T2);
  enif_release_binary(&ENiels);
  enif_release_binary(&B);
  return Extended2;
  }
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
  if((!checka) || (!(A.size == 128))){
    return(error_atom(env));
  };

  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 128, &Result);

  uint64_t * U = (uint64_t *)&A.data[0];
  uint64_t * V = (uint64_t *)&A.data[32];
  uint64_t * Z = (uint64_t *)&A.data[64];
  uint64_t * T = (uint64_t *)&A.data[96];

  uint64_t * Ub = (uint64_t *)&(C[0]);
  uint64_t * Vb = (uint64_t *)&(C[32]);
  uint64_t * Zb = (uint64_t *)&(C[64]);
  uint64_t * Tb = (uint64_t *)&(C[96]);

  //e_double2(U, V, Z, T1, T2,
             //          Ub, Vb, Zb, T1b, T2b);
  e_double2(U, V, Z, T,
            Ub, Vb, Zb, Tb);
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
  if((!checka) || (!(Extended.size == 128))){
    return(error_atom(env));
  };
  if((!checkb) || (!(ENiels.size == 128))){
    return(error_atom(env));
  };
  
  ERL_NIF_TERM Result;
  char * C = enif_make_new_binary
    (env, 128, &Result);

  uint64_t * X1 = (uint64_t *)&Extended.data[0];
  uint64_t * Y1 = (uint64_t *)&Extended.data[32];
  uint64_t * Z1 = (uint64_t *)&Extended.data[64];
  uint64_t * T1 = (uint64_t *)&Extended.data[96];

  uint64_t * X2 = (uint64_t *)&ENiels.data[0];
  uint64_t * Y2 = (uint64_t *)&ENiels.data[32];
  uint64_t * Z2 = (uint64_t *)&ENiels.data[64];
  uint64_t * T2 = (uint64_t *)&ENiels.data[96];

  uint64_t * X3 = (uint64_t *)&(C[0]);
  uint64_t * Y3 = (uint64_t *)&(C[32]);
  uint64_t * Z3 = (uint64_t *)&(C[64]);
  uint64_t * T3 = (uint64_t *)&(C[96]);

  e_add2(X1, Y1, Z1, T1,
         X2, Y2, Z2, T2,
         X3, Y3, Z3, T3);

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
   {"pmul", 2, e_mul},
   {"pmul_long", 2, e_mul_long},

   {"ctest", 1, ctest}
  };

ERL_NIF_INIT(c_ed,nif_funcs,NULL,NULL,NULL,NULL)
