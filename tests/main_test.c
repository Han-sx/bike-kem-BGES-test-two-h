/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0"
 *
 * Written by Nir Drucker, Shay Gueron and Dusan Kostic,
 * AWS Cryptographic Algorithms Group.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "gf2x.h"
#include "kem.h"
#include "measurements.h"
#include "utilities.h"
#include "cpu_features.h"

// 定义是否将未知数个数写入文件
#define W_FILE 0

#if !defined(NUM_OF_TESTS)
#  define NUM_OF_TESTS 1
#endif

typedef struct magic_number_s {
  uint64_t val[4];
} magic_number_t;

#define STRUCT_WITH_MAGIC(name, size) \
  struct {                            \
    magic_number_t magic1;            \
    uint8_t        val[size];         \
    magic_number_t magic2;            \
  }(name) = {magic, {0}, magic};

#define CHECK_MAGIC(param)                                          \
  if((0 != memcmp((param).magic1.val, magic.val, sizeof(magic))) || \
     (0 != memcmp((param).magic2.val, magic.val, sizeof(magic)))) { \
    printf("Magic is incorrect for param\n");                       \
  }

////////////////////////////////////////////////////////////////
//                 Main function for testing
////////////////////////////////////////////////////////////////
int main()
{
  // 定义未知数个数
  uint32_t x_count = 0;

  // Initialize the CPU features flags
  cpu_features_init();

#if defined(FIXED_SEED)
  srand(0);
#else
  srand(time(NULL));
#endif

  magic_number_t magic = {0xa1234567b1234567, 0xc1234567d1234567,
                          0xe1234567f1234567, 0x0123456711234567};

  STRUCT_WITH_MAGIC(sk, sizeof(sk_t));
  STRUCT_WITH_MAGIC(pk, sizeof(pk_t));
  STRUCT_WITH_MAGIC(ct, sizeof(ct_t));
  STRUCT_WITH_MAGIC(sk_two, sizeof(sk_t_two));
  STRUCT_WITH_MAGIC(pk_two, sizeof(pk_t_two));
  STRUCT_WITH_MAGIC(ct_two, sizeof(ct_t_two));
  STRUCT_WITH_MAGIC(k_enc, sizeof(ss_t)); // shared secret after decapsulate
  STRUCT_WITH_MAGIC(k_dec, sizeof(ss_t)); // shared secret after encapsulate

  for(size_t i = 1; i <= NUM_OF_TESTS; ++i) {
    int res = 0;
    int res_two = 0;

    printf("Code test: %lu\n", i);

    // Key generation
    MEASURE("  keypair", res = crypto_kem_keypair(pk.val, sk.val););

    // 增加辅助密钥生成
    // Key generation
    MEASURE("  keypair", res_two = crypto_kem_keypair_two(pk_two.val, sk_two.val););
  
    if(res != 0) {
      printf("Keypair failed with error: %d\n", res);
      continue;
    }

    if(res_two){}

    uint32_t dec_rc = 0;

    // Encapsulate
    // 此部分需要增加辅助密钥加密，输出 ct 和 辅助密文 ct_a
    MEASURE("  encaps", res = crypto_kem_enc(ct.val, ct_two.val, k_enc.val, pk.val, pk_two.val););
    if(res != 0) {
      printf("encapsulate failed with error: %d\n", res);
      continue;
    }

    // clock_t start_1 = clock();
    // Decapsulate
    // 此部分增加辅助密钥解密，将 ct 和 ct_a 输入到解密程序中
    MEASURE("  decaps", dec_rc = crypto_kem_dec(k_dec.val, ct.val, sk.val, &x_count););
    // clock_t end_1 = clock();
    // printf("\tDecapsulate took %lfs\n", ((double)(end_1 - start_1) / CLOCKS_PER_SEC));

    // Check test status
    if(dec_rc != 0) {
      printf("Decoding failed after %ld code tests!\n", i);
    } else {
      if(secure_cmp(k_enc.val, k_dec.val, sizeof(k_dec.val) / sizeof(uint64_t))) {
        printf("Success! decapsulated key is the same as encapsulated "
               "key!\n");
      } else {
        printf("Failure! decapsulated key is NOT the same as encapsulated "
               "key!\n");
      }
    }

    // Check magic numbers (memory overflow) 
    CHECK_MAGIC(sk);
    CHECK_MAGIC(pk);
    CHECK_MAGIC(ct);
    CHECK_MAGIC(k_enc);
    CHECK_MAGIC(k_dec);

    print("Initiator's generated key (K) of 256 bits = ", (uint64_t *)k_enc.val,
          SIZEOF_BITS(k_enc.val));
    print("Responder's computed key (K) of 256 bits  = ", (uint64_t *)k_dec.val,
          SIZEOF_BITS(k_enc.val));

    // 写入文件
    if(W_FILE == 1){
      FILE *fp_1;
      fp_1 = fopen("x_count.txt", "a");
      fprintf(fp_1, "%u,", x_count);
      fclose(fp_1);
      }
  }

  return 0;
}
