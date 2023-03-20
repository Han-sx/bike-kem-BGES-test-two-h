/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0"
 *
 * Written by Nir Drucker, Shay Gueron and Dusan Kostic,
 * AWS Cryptographic Algorithms Group.
 *
 * [1] The optimizations are based on the description developed in the paper:
 *     Drucker, Nir, and Shay Gueron. 2019. “A Toolbox for Software Optimization
 *     of QC-MDPC Code-Based Cryptosystems.” Journal of Cryptographic Engineering,
 *     January, 1–17. https://doi.org/10.1007/s13389-018-00200-4.
 *
 * [2] The decoder algorithm is the Black-Gray decoder in
 *     the early submission of CAKE (due to N. Sandrier and R Misoczki).
 *
 * [3] The analysis for the constant time implementation is given in
 *     Drucker, Nir, Shay Gueron, and Dusan Kostic. 2019.
 *     “On Constant-Time QC-MDPC Decoding with Negligible Failure Rate.”
 *     Cryptology EPrint Archive, 2019. https://eprint.iacr.org/2019/1289.
 *
 * [4] it was adapted to BGF in:
 *     Drucker, Nir, Shay Gueron, and Dusan Kostic. 2019.
 *     “QC-MDPC decoders with several shades of gray.”
 *     Cryptology EPrint Archive, 2019. To be published.
 *
 * [5] Chou, T.: QcBits: Constant-Time Small-Key Code-Based Cryptography.
 *     In: Gier-lichs, B., Poschmann, A.Y. (eds.) Cryptographic Hardware
 *     and Embedded Systems– CHES 2016. pp. 280–300. Springer Berlin Heidelberg,
 *     Berlin, Heidelberg (2016)
 *
 * [6] The rotate512_small funciton is a derivative of the code described in:
 *     Guimarães, Antonio, Diego F Aranha, and Edson Borin. 2019.
 *     “Optimized Implementation of QC-MDPC Code-Based Cryptography.”
 *     Concurrency and Computation: Practice and Experience 31 (18):
 *     e5089. https://doi.org/10.1002/cpe.5089.
 */

#include "decode.h"
#include "cleanup.h"
#include "decode_internal.h"
#include "gf2x.h"
#include "utilities.h"
#include <m4ri/m4ri.h>
#include <stdio.h>
#include <time.h>

// Decoding (bit-flipping) parameter
#if defined(BG_DECODER)
#  if(LEVEL == 1)
#    define MAX_IT 3
#  elif(LEVEL == 3)
#    define MAX_IT 4
#  else
#    error "Level can only be 1/3"
#  endif
#elif defined(BGF_DECODER)
#  define MAX_IT 5
#endif

#define GUSS_BLOCK  64
#define X_COUNT_MIN 7000

// 利用解出来的 b 和 ct 还原 fm(ct_verify)
_INLINE_ void solving_equations_mf(IN OUT e_t *ct_verify, IN uint32_t b[])
{
  // 放 0 用 '与', 放 1 用 '或'
  // 定义 11111111 和 00000001 用于计算
  uint8_t mask_255 = 255;
  uint8_t mask_1   = 1;
  int     bit_u    = 8;
  // 对第一组操作
  for(int i_v = 0; i_v < R_BITS; i_v++) {
    if(b[i_v] != 0) {
      b[i_v] = b[i_v] % 2;
      if(b[i_v] == 0) {
        // 用与操作
        ct_verify->val[0].raw[i_v / bit_u] =
          (mask_255 ^ (mask_1 << (i_v % bit_u))) &
          ct_verify->val[0].raw[i_v / bit_u];
      } else {
        // 用或操作
        ct_verify->val[0].raw[i_v / bit_u] =
          (mask_1 << (i_v % bit_u)) | ct_verify->val[0].raw[i_v / bit_u];
      }
    }
  }
  // 对第二组操作
  for(int i_v = R_BITS; i_v < 2 * R_BITS; i_v++) {
    if(b[i_v] != 0) {
      b[i_v] = b[i_v] % 2;
      if(b[i_v] == 0) {
        // 用与操作
        ct_verify->val[1].raw[(i_v - R_BITS) / bit_u] =
          (mask_255 ^ (mask_1 << ((i_v - R_BITS) % bit_u))) &
          ct_verify->val[1].raw[(i_v - R_BITS) / bit_u];
      } else {
        // 用或操作
        ct_verify->val[1].raw[(i_v - R_BITS) / bit_u] =
          (mask_1 << ((i_v - R_BITS) % bit_u)) |
          ct_verify->val[1].raw[(i_v - R_BITS) / bit_u];
      }
    }
  }
}

// 8 位异或
_INLINE_ ret_t xor_8(OUT uint64_t      *res,
                     IN const uint64_t *a,
                     IN const uint64_t *b,
                     IN const uint64_t  bytelen,
                     IN const uint64_t  r_bytelen)
{
  for(uint64_t i = r_bytelen; i < bytelen; i++) {
    res[i] = a[i] ^ b[i];
  }
  return SUCCESS;
}

// 用于交换两个数组
_INLINE_ void
swap(OUT uint64_t *a, OUT uint64_t *b, uint32_t eq_j, uint32_t guss_j_num)
{
  uint64_t tmp_guss[guss_j_num];
  for(uint32_t change_i = eq_j; change_i < guss_j_num; change_i++) {
    tmp_guss[change_i] = a[change_i];
    a[change_i]        = b[change_i];
    b[change_i]        = tmp_guss[change_i];
  }
}

// 对两个数组进行或操作
// c = ((a | b) | c)
_INLINE_ void array_or(OUT uint8_t      *c,
                       IN const uint8_t *a,
                       IN const uint8_t *b,
                       IN const uint64_t bytelen)
{
  for(uint64_t i = 0; i < bytelen; i++) {
    c[i] = a[i] | b[i] | c[i];
  }
}

ret_t compute_syndrome(OUT syndrome_t      *syndrome,
                       IN const pad_r_t    *c0,
                       IN const pad_r_t    *h0,
                       IN const decode_ctx *ctx)
{
  DEFER_CLEANUP(pad_r_t pad_s, pad_r_cleanup);

  gf2x_mod_mul(&pad_s, c0, h0);

  bike_memcpy((uint8_t *)syndrome->qw, pad_s.val.raw, R_BYTES);
  ctx->dup(syndrome);

  return SUCCESS;
}

_INLINE_ ret_t recompute_syndrome(OUT syndrome_t      *syndrome,
                                  IN const pad_r_t    *c0,
                                  IN const pad_r_t    *h0,
                                  IN const pad_r_t    *pk,
                                  IN const e_t        *e,
                                  IN const decode_ctx *ctx)
{
  DEFER_CLEANUP(pad_r_t tmp_c0, pad_r_cleanup);
  DEFER_CLEANUP(pad_r_t e0 = {0}, pad_r_cleanup);
  DEFER_CLEANUP(pad_r_t e1 = {0}, pad_r_cleanup);

  e0.val = e->val[0];
  e1.val = e->val[1];

  // tmp_c0 = pk * e1 + c0 + e0
  gf2x_mod_mul(&tmp_c0, &e1, pk);
  gf2x_mod_add(&tmp_c0, &tmp_c0, c0);
  gf2x_mod_add(&tmp_c0, &tmp_c0, &e0);

  // Recompute the syndrome using the updated ciphertext
  GUARD(compute_syndrome(syndrome, &tmp_c0, h0, ctx));

  return SUCCESS;
}

_INLINE_ uint8_t get_threshold(IN const syndrome_t *s)
{
  bike_static_assert(sizeof(*s) >= sizeof(r_t), syndrome_is_large_enough);

  const uint32_t syndrome_weight = r_bits_vector_weight((const r_t *)s->qw);

  // The equations below are defined in BIKE's specification p. 16, Section 5.2
  uint32_t       thr  = THRESHOLD_COEFF0 + (THRESHOLD_COEFF1 * syndrome_weight);
  const uint32_t mask = secure_l32_mask(thr, THRESHOLD_MIN);
  thr = (u32_barrier(mask) & thr) | (u32_barrier(~mask) & THRESHOLD_MIN);

  DMSG("    Threshold: %d\n", thr);
  return thr;
}

// Calculate the Unsatisfied Parity Checks (UPCs) and update the errors
// vector (e) accordingly. In addition, update the black and gray errors vector
// with the relevant values.
_INLINE_ void find_err1(OUT e_t                       *e,
                        OUT e_t                       *black_e,
                        OUT e_t                       *gray_e,
                        IN const syndrome_t           *syndrome,
                        IN const compressed_idx_d_ar_t wlist,
                        IN const uint8_t               threshold,
                        IN const decode_ctx           *ctx,
                        IN const uint8_t               delat)
{
  // This function uses the bit-slice-adder methodology of [5]:
  DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
  DEFER_CLEANUP(upc_t upc, upc_cleanup);

  for(uint32_t i = 0; i < N0; i++) {
    // UPC must start from zero at every iteration
    bike_memset(&upc, 0, sizeof(upc));

    // 1) Right-rotate the syndrome for every secret key set bit index
    //    Then slice-add it to the UPC array.
    for(size_t j = 0; j < D; j++) {
      ctx->rotate_right(&rotated_syndrome, syndrome, wlist[i].val[j]);
      ctx->bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
    }

    // 2) Subtract the threshold from the UPC counters
    ctx->bit_slice_full_subtract(&upc, threshold);

    // 3) Update the errors and the black errors vectors.
    //    The last slice of the UPC array holds the MSB of the accumulated values
    //    minus the threshold. Every zero bit indicates a potential error bit.
    //    The errors values are stored in the black array and xored with the
    //    errors Of the previous iteration.
    const r_t *last_slice = &(upc.slice[SLICES - 1].u.r.val);
    for(size_t j = 0; j < R_BYTES; j++) {
      const uint8_t sum_msb  = (~last_slice->raw[j]);
      black_e->val[i].raw[j] = sum_msb;
      e->val[i].raw[j] ^= sum_msb;
    }

    // Ensure that the padding bits (upper bits of the last byte) are zero so
    // they will not be included in the multiplication and in the hash function.
    e->val[i].raw[R_BYTES - 1] &= LAST_R_BYTE_MASK;

    // 4) Calculate the gray error array by adding "DELTA" to the UPC array.
    //    For that we reuse the rotated_syndrome variable setting it to all "1".
    for(size_t l = 0; l < delat; l++) {
      bike_memset((uint8_t *)rotated_syndrome.qw, 0xff, R_BYTES);
      ctx->bit_sliced_adder(&upc, &rotated_syndrome, SLICES);
    }

    // 5) Update the gray list with the relevant bits that are not
    //    set in the black list.
    for(size_t j = 0; j < R_BYTES; j++) {
      const uint8_t sum_msb = (~last_slice->raw[j]);
      gray_e->val[i].raw[j] = (~(black_e->val[i].raw[j])) & sum_msb;
    }
  }
}

// Recalculate the UPCs and update the errors vector (e) according to it
// and to the black/gray vectors.
_INLINE_ void find_err2(OUT e_t                       *e,
                        IN e_t                        *pos_e,
                        IN const syndrome_t           *syndrome,
                        IN const compressed_idx_d_ar_t wlist,
                        IN const uint8_t               threshold,
                        IN const decode_ctx           *ctx)
{
  DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
  DEFER_CLEANUP(upc_t upc, upc_cleanup);

  for(uint32_t i = 0; i < N0; i++) {
    // UPC must start from zero at every iteration
    bike_memset(&upc, 0, sizeof(upc));

    // 1) Right-rotate the syndrome, for every index of a set bit in the secret
    // key. Then slice-add it to the UPC array.
    for(size_t j = 0; j < D; j++) {
      ctx->rotate_right(&rotated_syndrome, syndrome, wlist[i].val[j]);
      ctx->bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
    }

    // 2) Subtract the threshold from the UPC counters
    ctx->bit_slice_full_subtract(&upc, threshold);

    // 3) Update the errors vector.
    //    The last slice of the UPC array holds the MSB of the accumulated values
    //    minus the threshold. Every zero bit indicates a potential error bit.
    const r_t *last_slice = &(upc.slice[SLICES - 1].u.r.val);
    for(size_t j = 0; j < R_BYTES; j++) {
      const uint8_t sum_msb = (~last_slice->raw[j]);
      e->val[i].raw[j] ^= (pos_e->val[i].raw[j] & sum_msb);
    }

    // Ensure that the padding bits (upper bits of the last byte) are zero, so
    // they are not included in the multiplication, and in the hash function.
    e->val[i].raw[R_BYTES - 1] &= LAST_R_BYTE_MASK;
  }
}

ret_t decode(OUT e_t *e, IN const ct_t *ct, IN const sk_t *sk)
{
  // Initialize the decode methods struct
  decode_ctx ctx;
  decode_ctx_init(&ctx);

  // 定义 BGF 译码 delta
  uint8_t delta = DELTA;
  // 定义解方程译码 delta
  uint8_t delta_eq        = DELTA_EQ;
  uint8_t delta_eq_step23 = DELTA_EQ_STEP23;

  DEFER_CLEANUP(e_t black_e = {0}, e_cleanup);
  DEFER_CLEANUP(e_t gray_e = {0}, e_cleanup);

  // 构建用于存放未知数的解方程黑灰集合
  DEFER_CLEANUP(e_t e_eq = {0}, e_cleanup);
  DEFER_CLEANUP(e_t black_e_eq = {0}, e_cleanup);
  DEFER_CLEANUP(e_t gray_e_eq = {0}, e_cleanup);

  // 新建黑灰集合的'或'集合
  DEFER_CLEANUP(e_t black_or_gray_e = {0}, e_cleanup);

  DEFER_CLEANUP(pad_r_t c0 = {0}, pad_r_cleanup);
  DEFER_CLEANUP(pad_r_t h0 = {0}, pad_r_cleanup);
  pad_r_t pk = {0};

  // Pad ciphertext (c0), secret key (h0), and public key (h)
  c0.val = ct->c0;
  h0.val = sk->bin[0];
  pk.val = sk->pk;

  DEFER_CLEANUP(syndrome_t s = {0}, syndrome_cleanup);
  DMSG("  Computing s.\n");
  GUARD(compute_syndrome(&s, &c0, &h0, &ctx));
  ctx.dup(&s);

  // Reset (init) the error because it is xored in the find_err functions.
  bike_memset(e, 0, sizeof(*e));

  for(uint32_t iter = 0; iter < MAX_IT; iter++) {
    const uint8_t threshold = get_threshold(&s);

    DMSG("    Iteration: %d\n", iter);
    DMSG("    Weight of e: %lu\n",
         r_bits_vector_weight(&e->val[0]) + r_bits_vector_weight(&e->val[1]));
    DMSG("    Weight of syndrome: %lu\n", r_bits_vector_weight((r_t *)s.qw));

    // 获取解方程的未知数黑灰集合
    find_err1(&e_eq, &black_e_eq, &gray_e_eq, &s, sk->wlist, threshold, &ctx,
              delta_eq);

    find_err1(e, &black_e, &gray_e, &s, sk->wlist, threshold, &ctx, delta);

    // 将获取的黑集合与灰集合'或'操作
    for(uint8_t i = 0; i < N0; i++) {
      array_or((uint8_t *)&black_or_gray_e.val[i].raw, black_e_eq.val[i].raw,
               gray_e_eq.val[i].raw, R_BYTES);
    }

    GUARD(recompute_syndrome(&s, &c0, &h0, &pk, e, &ctx));
#if defined(BGF_DECODER)
    if(iter >= 1) {
      continue;
    }
#endif
    DMSG("    Weight of e: %lu\n",
         r_bits_vector_weight(&e->val[0]) + r_bits_vector_weight(&e->val[1]));
    DMSG("    Weight of syndrome: %lu\n", r_bits_vector_weight((r_t *)s.qw));

    // 选取 step2 的黑灰集合
    find_err1(&e_eq, &black_e_eq, &gray_e_eq, &s, sk->wlist, ((D + 1) / 2) + 1,
              &ctx, delta_eq_step23);

    // 将获取的黑集合与灰集合'或'操作
    for(uint8_t i = 0; i < N0; i++) {
      array_or((uint8_t *)&black_or_gray_e.val[i].raw, black_e_eq.val[i].raw,
               gray_e_eq.val[i].raw, R_BYTES);
    }

    find_err2(e, &black_e, &s, sk->wlist, ((D + 1) / 2) + 1, &ctx);
    GUARD(recompute_syndrome(&s, &c0, &h0, &pk, e, &ctx));

    DMSG("    Weight of e: %lu\n",
         r_bits_vector_weight(&e->val[0]) + r_bits_vector_weight(&e->val[1]));
    DMSG("    Weight of syndrome: %lu\n", r_bits_vector_weight((r_t *)s.qw));

    // 选取 step3 的黑灰集合
    find_err1(&e_eq, &black_e_eq, &gray_e_eq, &s, sk->wlist, ((D + 1) / 2) + 1,
              &ctx, delta_eq_step23);

    // 将获取的黑集合与灰集合'或'操作
    for(uint8_t i = 0; i < N0; i++) {
      array_or((uint8_t *)&black_or_gray_e.val[i].raw, black_e_eq.val[i].raw,
               gray_e_eq.val[i].raw, R_BYTES);
    }

    find_err2(e, &gray_e, &s, sk->wlist, ((D + 1) / 2) + 1, &ctx);
    GUARD(recompute_syndrome(&s, &c0, &h0, &pk, e, &ctx));
  }

  // ===========================进行方程组求解算法===============================

  // clock_t start_3;
  // clock_t end_3;

  // --------------------- 1.构建方程组 ---------------------
  // start_3 = clock();

  // 新建 b 常数
  DEFER_CLEANUP(pad_r_t b = {0}, pad_r_cleanup);
  // 新建 sk 的转置
  sk_t sk_transpose = {0};

  // 将 c0 和 h0 相乘得到方程右边的增广 b 常数
  gf2x_mod_mul(&b, &c0, &h0);

  // 填充未知数个数为固定值
  uint32_t x_count_pad =
    (X_COUNT_MIN - (r_bits_vector_weight((r_t *)black_or_gray_e.val[0].raw) +
                    r_bits_vector_weight((r_t *)black_or_gray_e.val[1].raw))) /
    8;

  for(uint32_t i_x_count = 0; i_x_count < x_count_pad / 2 + 1; i_x_count++) {
    black_or_gray_e.val[0].raw[i_x_count] = 255;
    black_or_gray_e.val[1].raw[i_x_count] = 255;
  }

  // 获取未知数的个数
  uint32_t x_weight = r_bits_vector_weight((r_t *)black_or_gray_e.val[0].raw) +
                      r_bits_vector_weight((r_t *)black_or_gray_e.val[1].raw);

  // printf("\n未知数个数: %u\n", x_weight);

  // 构造 sk 转置 sk_transpose, 获取 sk 转置的首行索引
  // 𝜑(A)' = a0 + ar-1X + ar-2X^2 ...
  for(uint8_t i = 0; i < N0; i++) {
    for(uint8_t i_DV = 0; i_DV < D; i_DV++) {
      if(sk->wlist[i].val[i_DV] != 0) {
        sk_transpose.wlist[i].val[i_DV] = R_BITS - sk->wlist[i].val[i_DV];
      } else {
        sk_transpose.wlist[i].val[i_DV] = sk->wlist[i].val[i_DV];
      }
    }
  }

  // 对方程组未知数进行构建，将 x0-xall 的对应关系列出来
  // black_or_gray_e 的每个位置对应 旋转 h 的位置满足 (e+r-h) % r
  // 对每个 black_or_gray_e 进行 and 寻找是否存在未知数
  // guss_j_num 最后一个字用来存储 b

  uint32_t guss_j_num = 0;
  if(x_weight % GUSS_BLOCK == 0) {
    guss_j_num = x_weight / GUSS_BLOCK + 1;
  } else {
    guss_j_num = x_weight / GUSS_BLOCK + 2;
  }
  uint64_t equations_guss_byte[R_BITS][guss_j_num];
  memset(equations_guss_byte, 0, sizeof(equations_guss_byte));

  uint8_t  mask_e       = 1;
  uint64_t mask_e_byte  = 1;
  uint32_t e_count      = 0;
  uint32_t e_index      = 0;
  uint32_t e_index_byte = 0;
  // 保存每个 x 对应的位置
  uint32_t x_arr[x_weight];
  memset(x_arr, 0, sizeof(x_arr));

  // 填充 equations_guss_byte
  for(uint8_t i = 0; i < N0; i++) {
    for(uint32_t i_e_x = 0; i_e_x < R_BITS; i_e_x++) {
      if(i_e_x % 8 == 0) {
        mask_e  = 1;
        e_index = i_e_x / 8;
      }
      if((mask_e & black_or_gray_e.val[i].raw[e_index]) != 0) {
        if(e_count % GUSS_BLOCK == 0) {
          mask_e_byte  = 1;
          e_index_byte = e_count / GUSS_BLOCK;
        }
        uint32_t e_add_R = i_e_x + R_BITS;
        x_arr[e_count]   = i_e_x + i * R_BITS;
        e_count += 1;
        // 根据 e 的和 h 的位置来确定 equations_guss_byte 的构建 (e+r-h) % r
        for(uint32_t wlist_i = 0; wlist_i < D; wlist_i++) {
          equations_guss_byte[(e_add_R - sk_transpose.wlist[i].val[wlist_i]) %
                              R_BITS][e_index_byte] += mask_e_byte;
        }
        mask_e_byte <<= 1;
      }
      mask_e <<= 1;
    }
  }

  // equations_guss_byte 最后加入常数列
  for(uint32_t i = 0; i < R_BYTES - 1; i++) {
    for(uint8_t index = 0, location = 1; location != 0; location <<= 1) {
      if((b.val.raw[i] & location) != 0) {
        equations_guss_byte[8 * i + index][guss_j_num - 1] = 1;
      }
      index++;
    }
  }
  // 处理溢出位
  for(uint8_t index = 0, location = 1; location <= MASK(LAST_R_BYTE_LEAD);
      location <<= 1) {
    if((b.val.raw[R_BYTES - 1] & location) != 0) {
      equations_guss_byte[8 * (R_BYTES - 1) + index][guss_j_num - 1] = 1;
    }
    index++;
  }

  // end_3 = clock();
  // printf("\t 构建 took %lfs\n", ((double)(end_3 - start_3) / CLOCKS_PER_SEC));

  // ===================================== m4ri 解方程 ==========================

  // clock_t start_m;
  // clock_t end_m;
  // start_m = clock();
  // 求解 AX=B
  // 构造 A B
  mzd_t *A = mzd_init(R_BITS, x_weight);
  mzd_t *B = mzd_init(R_BITS, 1);
  // 给 A 填充信息
  wi_t const width_A    = A->width - 1;
  word const mask_end_A = A->high_bitmask;
  for(rci_t i = 0; i < A->nrows; ++i) {
    word *row = mzd_row(A, i);
    for(wi_t j = 0; j < width_A; ++j)
      row[j] = ((uint64_t *)(equations_guss_byte[i]))[j];
    row[width_A] ^=
      (row[width_A] ^ ((uint64_t *)equations_guss_byte[i])[width_A]) & mask_end_A;
  }
  __M4RI_DD_MZD(A);

  // 给 B 填充信息
  wi_t const width_B    = B->width - 1;
  word const mask_end_B = B->high_bitmask;
  for(rci_t i = 0; i < B->nrows; ++i) {
    word *row = mzd_row(B, i);
    for(wi_t j = 0; j < width_B; ++j)
      row[j] = ((uint64_t *)(equations_guss_byte[i]))[width_A + 1];
    row[width_B] ^=
      (row[width_B] ^ ((uint64_t *)equations_guss_byte[i])[width_A + 1]) &
      mask_end_B;
  }
  __M4RI_DD_MZD(B);

  int consistency = mzd_solve_left(A, B, 0, 0);

  if(consistency == -1) {
    // printf("failed (solution should have been found)\n");
  } else {
    // printf("m4ri 求解成功\n");
  }

  // end_m = clock();
  // printf("\t m4ri 求解 took %lfs\n",
  //        ((double)(end_m - start_m) / CLOCKS_PER_SEC));

  // 构造m4ri解数组
  uint32_t x_m4[2 * R_BITS] = {0};

  // 将结果从 B 中取出来
  for(uint32_t i = 0; i < x_weight; i++) {
    word const *row = mzd_row_const(B, i);
    if((row[0] & 1) == 1){
      x_m4[x_arr[i]] = 1;
    }else{
      x_m4[x_arr[i]] = 2;
    }
  }

  e_t e_v_m4 = {0};
  solving_equations_mf((e_t *)&e_v_m4, x_m4);

  DEFER_CLEANUP(syndrome_t s_v_m4 = {0}, syndrome_cleanup);

  GUARD(recompute_syndrome(&s_v_m4, &c0, &h0, &pk, &e_v_m4, &ctx));

  // m4ri失败则输出错误
  if(r_bits_vector_weight((r_t *)s_v_m4.qw) > 0) {
    // printf("\nm4ri译码失败\n");
  } else {
    // printf("\nm4ri译码成功\n");
  }

  // 译码失败返回错误
  if(r_bits_vector_weight((r_t *)s.qw) > 0) {
    // printf("\nBGF译码失败\n");
    BIKE_ERROR(E_DECODING_FAILURE);
  }

  // printf("\nBGF译码成功\n");

  return SUCCESS;
}
