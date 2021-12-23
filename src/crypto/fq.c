#include <erl_nif.h>
#include <stdio.h>
#include <stdint.h>
//#include <inttypes.h>

//todo. it looks like we can make subtraction almost two times faster if erlang stored each binary in reverse.

//#define Max64 18446744073709551615

//2^64 - 1
//const uint64_t Max64 = 18446744073709551615U;

//2^51
//const uint64_t Max51 = 2251799813685248U;

//2^32 - 1
const uint64_t Max32 = 4294967295U;

//q
const uint32_t q[8] =
  {1944954707,698187080,859428872,161601541,
   1404937218,4294859774,4294967295,1};

uint32_t A[8];
uint32_t B[8];
uint32_t C[8];
int carry = 0;
int32_t arr[2];
unsigned char resultchars[32];
ErlNifBinary resultnif;
ErlNifBinary bin;
unsigned char bin2[32];//used to reverse the array of characters, before we can make it into an array of 32-bit numbers.

//uint32_t * nb2[8];
//int result = enif_alloc_binary(32, &bin);
//int ignore0 = enif_alloc_binary//0.25
//  (32, &resultnif);

//typedef struct {
//    size_t size;
//    unsigned char* data;
//} ErlNifBinary;


//add carry
uint64_t d;
void adc(uint32_t a, uint32_t b, uint32_t c, uint32_t arr[])
{
  d = a;
  d += b;
  d += c;
  //uint64_t d = a + b + c;
  //printf("adc %lu \n", d);
  arr[0] = d;//value
  //uint64_t carry = d >> 32;
  arr[1] = d >> 32;//carry
}

//subtract borrow
uint64_t e;
void sbb(uint32_t a, uint32_t b, uint32_t borrow, uint32_t arr[])
{
  e = b;
  e += borrow;
  //printf("subtracting %lu %lu \n", d, e);
  arr[0] = a - e;
  arr[1] = (a < e);
}

void read_bin(ErlNifEnv* env, ERL_NIF_TERM arg0, uint32_t * nb3)
{
  //ErlNifBinary bin;
  //int result = enif_alloc_binary
  //  (32, &bin);
  int inspect_result = enif_inspect_binary//0.03
    (env, arg0, &bin);
  for(int i = 0; i<32; i++){//0.07
    bin2[31-i] = bin.data[i];
  }
  //enif_release_binary(&bin);
  uint32_t * nb2  = (uint32_t *)bin2;//0.02
  //nb2  = (uint32_t *)bin2;
  //uint32_t nb3[8];
  for(int i = 0; i<8; i++){
    nb3[7-i] = nb2[i];
  }
}

void write_bin(const uint32_t * a, char * c){//0.03
  for(int i = 0; i<8; i++){
    for(int j = 0; j<4; j++){
      c[(4*i)+j] = a[i] >> (8*(3-j));
    };
  };
}

int greater_than(const uint32_t * a,
                 const uint32_t * b)
{
  for(int i = 0; i<8; i++){
    if(a[i] > b[i]){return(1);}
    else if(a[i] < b[i]){return(0);}
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
  // int32_t arr[2];
  for(int i = 7; i>-1; i--){
    sbb(a[i], b[i], carry, arr);
    carry = arr[1];
    c[i] = arr[0];
  };
};
void assume_safe_add
(const uint32_t * a,
 const uint32_t * b,
 uint32_t * c){
  carry = 0;
  //int32_t arr[2];
  for(int i = 7; i>-1; i--){
    adc(a[i], b[i], carry, arr);
    carry = arr[1];
    c[i] = arr[0];
  }
};

static ERL_NIF_TERM setup
(ErlNifEnv* env,
 int argc,
 const ERL_NIF_TERM argv[])
{
  //only runs once at the beginning.
  int result = enif_alloc_binary
    (32, &bin);
  int result2 = enif_alloc_binary
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

static ERL_NIF_TERM sub(ErlNifEnv* env,
                        int argc,
                        const ERL_NIF_TERM argv[])
{
  //printf("many args %i \n", argc);
  //uint32_t arr[2];
  //adc(Max32, 2, 10, arr);
  //printf("test adc: %u carry: %u \n", arr[0], arr[1]);
  //sbb(2, 3, 0, arr);
  //printf("test sbb: %u borrow: %u \n", arr[0], arr[1]);


  read_bin(env, argv[0], A);//0.06
  read_bin(env, argv[1], B);

  sub2(A, B, C);//0.05 - 0.1
  
  //write_bin(C, resultchars);//0.1
  write_bin(C, bin2);//0.1

  //  ErlNifBinary resultnif;
  //  int result = enif_alloc_binary//0.25
  // (32, &resultnif);
  //resultnif.size = 32;
  //resultnif.data = resultchars;
  resultnif.data = bin2;

  ERL_NIF_TERM finalresult = enif_make_binary//0.05
    (env, &resultnif);

  //return argv[0];
  return finalresult;
}

static ErlNifFunc nif_funcs[] =
  {
   {"sub", 2, sub},
   {"setup", 1, setup}
  };

ERL_NIF_INIT(fq,nif_funcs,NULL,NULL,NULL,NULL)
