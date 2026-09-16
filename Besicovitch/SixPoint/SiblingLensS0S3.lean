/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.SixPoint.RationalChord
public import Besicovitch.SixPoint.SiblingIncidenceLedger

/-!
# The `S0/S3` sibling incidence

This file closes the balanced/balanced orbit `S0/S3`. A common quadratic tangent controls the
three positive cross distances. Two secants of the square root retain enough of the two larger
radial penalties, and three exact rational sums of squared norms cover the resulting radial ranges.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace Besicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real linear combination of five vectors has nonnegative squared norm, expanded through
their Gram entries. -/
private theorem s0s3_norm_sq_nonneg (a b c d f : ℝ) (e p₁ p₂ w₁ w₂ : E) :
    0 ≤ a ^ 2 * ‖e‖ ^ 2 + b ^ 2 * ‖p₁‖ ^ 2 + c ^ 2 * ‖p₂‖ ^ 2 + d ^ 2 * ‖w₁‖ ^ 2 +
      f ^ 2 * ‖w₂‖ ^ 2 + 2 * a * b * ⟪e, p₁⟫_ℝ + 2 * a * c * ⟪e, p₂⟫_ℝ +
      2 * a * d * ⟪e, w₁⟫_ℝ + 2 * a * f * ⟪e, w₂⟫_ℝ + 2 * b * c * ⟪p₁, p₂⟫_ℝ +
      2 * b * d * ⟪p₁, w₁⟫_ℝ + 2 * b * f * ⟪p₁, w₂⟫_ℝ + 2 * c * d * ⟪p₂, w₁⟫_ℝ +
      2 * c * f * ⟪p₂, w₂⟫_ℝ + 2 * d * f * ⟪w₁, w₂⟫_ℝ := by
  have h := sq_nonneg ‖a • e + b • p₁ + c • p₂ + d • w₁ + f • w₂‖
  rw [← real_inner_self_eq_norm_sq] at h
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, RCLike.conj_to_real] at h
  rw [real_inner_comm e p₁, real_inner_comm e p₂, real_inner_comm e w₁, real_inner_comm e w₂,
    real_inner_comm p₁ p₂, real_inner_comm p₁ w₁, real_inner_comm p₁ w₂,
    real_inner_comm p₂ w₁, real_inner_comm p₂ w₂, real_inner_comm w₁ w₂] at h
  nlinarith [h]

private theorem s0s3_norm_sub_sub_sq (e x y : E) :
    ‖e - x - y‖ ^ 2 = ‖e‖ ^ 2 + ‖x‖ ^ 2 + ‖y‖ ^ 2 -
      2 * ⟪e, x⟫_ℝ - 2 * ⟪e, y⟫_ℝ + 2 * ⟪x, y⟫_ℝ := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left]
  ring

private theorem s0s3_gram_low_low (e p₁ p₂ w₁ w₂ : E) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 11930 / 543 * (‖p₁‖ ^ 2 + ‖w₂‖ ^ 2) -
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      1157 / 50 * ‖e‖ ^ 2 + 1263 / 50 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) -
        871 / 100 * (‖p₁ - p₂‖ ^ 2 + ‖w₁ - w₂‖ ^ 2) := by
  rw [s0s3_norm_sub_sub_sq, s0s3_norm_sub_sub_sq, s0s3_norm_sub_sub_sq, norm_sub_sq_real,
    norm_sub_sq_real]
  linarith [s0s3_norm_sq_nonneg (3511 / 1000) (41 / 40) (41 / 20) (41 / 20) (41 / 40) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 (733 / 250) (2253 / 1000) (-243 / 125) (-179 / 500) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 (843 / 500) (-203 / 100) (-2903 / 1000) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 (69 / 500) (67 / 500) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 0 1 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 1 0 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 1 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 0 1 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 0 0 1 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 1 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 0 (-1) 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 0 0 (-1) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 1 (-1) 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 1 0 (-1) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 1 1 e p₁ p₂ w₁ w₂,
    sq_nonneg ‖e‖, sq_nonneg ‖p₁‖, sq_nonneg ‖p₂‖, sq_nonneg ‖w₁‖, sq_nonneg ‖w₂‖]

private theorem s0s3_gram_low_high (e p₁ p₂ w₁ w₂ : E) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 11930 / 543 * ‖p₁‖ ^ 2 -
        1193 / 85 * ‖w₂‖ ^ 2 - 1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      621 / 25 * ‖e‖ ^ 2 + 2701 / 100 * ‖p₂‖ ^ 2 + 1863 / 100 * ‖w₁‖ ^ 2 -
        849 / 100 * ‖p₁ - p₂‖ ^ 2 - 131 / 25 * ‖w₁ - w₂‖ ^ 2 := by
  rw [s0s3_norm_sub_sub_sq, s0s3_norm_sub_sub_sq, s0s3_norm_sub_sub_sq, norm_sub_sq_real,
    norm_sub_sq_real]
  linarith [s0s3_norm_sq_nonneg (1873 / 500) (961 / 1000) (961 / 500) (961 / 500) (961 / 1000)
      e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 (2991 / 1000) (2221 / 1000) (-1821 / 1000) (-309 / 1000) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 (1169 / 500) (-139 / 100) (-509 / 250) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 (29 / 200) (-1 / 500) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 0 1 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 1 0 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 1 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 0 1 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 0 0 1 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 (-1) 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 0 (-1) 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 0 0 1 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 1 1 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 1 0 (-1) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 1 1 e p₁ p₂ w₁ w₂,
    sq_nonneg ‖e‖, sq_nonneg ‖p₁‖, sq_nonneg ‖p₂‖, sq_nonneg ‖w₁‖, sq_nonneg ‖w₂‖]

private theorem s0s3_gram_high_high (e p₁ p₂ w₁ w₂ : E) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 1193 / 85 * (‖p₁‖ ^ 2 + ‖w₂‖ ^ 2) -
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      2641 / 100 * ‖e‖ ^ 2 + 2071 / 100 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) -
        517 / 100 * (‖p₁ - p₂‖ ^ 2 + ‖w₁ - w₂‖ ^ 2) := by
  rw [s0s3_norm_sub_sub_sq, s0s3_norm_sub_sub_sq, s0s3_norm_sub_sub_sq, norm_sub_sq_real,
    norm_sub_sq_real]
  linarith [s0s3_norm_sq_nonneg (79 / 20) (911 / 1000) (1823 / 1000) (1823 / 1000) (911 / 1000)
      e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 (2103 / 1000) (417 / 250) (-2501 / 1000) (-79 / 200) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 (1119 / 500) (-1229 / 1000) (-257 / 125) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 (157 / 1000) (-11 / 250) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 0 1 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 1 0 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 (-1) 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 0 (-1) 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 1 0 0 0 1 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 1 0 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 0 (-1) 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 1 0 0 1 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 1 (-1) 0 e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 1 0 (-1) e p₁ p₂ w₁ w₂,
    s0s3_norm_sq_nonneg 0 0 0 1 1 e p₁ p₂ w₁ w₂,
    sq_nonneg ‖e‖, sq_nonneg ‖p₁‖, sq_nonneg ‖p₂‖, sq_nonneg ‖w₁‖, sq_nonneg ‖w₂‖]

private theorem s0s3_gram_high_low (e p₁ p₂ w₁ w₂ : E) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 1193 / 85 * ‖p₁‖ ^ 2 -
        11930 / 543 * ‖w₂‖ ^ 2 - 1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      621 / 25 * ‖e‖ ^ 2 + 1863 / 100 * ‖p₂‖ ^ 2 + 2701 / 100 * ‖w₁‖ ^ 2 -
        131 / 25 * ‖p₁ - p₂‖ ^ 2 - 849 / 100 * ‖w₁ - w₂‖ ^ 2 := by
  have h := s0s3_gram_low_high e w₂ w₁ p₂ p₁
  rw [sub_right_comm e w₂ p₂, sub_right_comm e w₁ p₂, sub_right_comm e w₁ p₁,
    norm_sub_rev w₂ w₁, norm_sub_rev p₂ p₁] at h
  linarith

omit [InnerProductSpace ℝ E] in
private theorem s0s3_positive_distances_le (e p₁ p₂ w₁ w₂ : E) :
    17 * ‖e - p₁ - w₁‖ + 20 * ‖e - p₂ - w₁‖ +
        17 * ‖e - p₂ - w₂‖ ≤
      815 / 12 + 18 / 5 * (‖e - p₁ - w₁‖ ^ 2 +
        ‖e - p₂ - w₁‖ ^ 2 + ‖e - p₂ - w₂‖ ^ 2) := by
  have h₁₁ := weightedNorm_le_quadratic (e - p₁ - w₁) 17 (18 / 5) (by norm_num)
  have h₂₁ := weightedNorm_le_quadratic (e - p₂ - w₁) 20 (18 / 5) (by norm_num)
  have h₂₂ := weightedNorm_le_quadratic (e - p₂ - w₂) 17 (18 / 5) (by norm_num)
  norm_num at h₁₁ h₂₁ h₂₂ ⊢
  linarith

private theorem secant_le (x lower upper : ℝ) (hlower : lower ≤ x) (hupper : x ≤ upper)
    (hsum : 0 < lower + upper) :
    (x ^ 2 + lower * upper) / (lower + upper) ≤ x := by
  rw [div_le_iff₀ hsum]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlower)
    (sub_nonpos.mpr hupper)]

private theorem s0s3_radius_floor {E : Type*} [NormedAddCommGroup E] (x y : E)
    (hy : ‖y‖ ≤ 1) (hseparation : barC ≤ ‖x - y‖) :
    193 / 500 ≤ ‖x‖ := by
  have htriangle := norm_sub_le x y
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  linarith

private theorem s0s3_low_radial_secant (x : ℝ) (hlower : 193 / 500 ≤ x)
    (hupper : x ≤ 1) :
    1930 / 693 * x ^ 2 + 37249 / 34650 ≤ 193 / 50 * x := by
  have h := secant_le x (193 / 500) 1 hlower hupper (by norm_num)
  norm_num at h ⊢
  linarith

private theorem s0s3_high_radial_low_secant (x : ℝ) (hlower : 193 / 500 ≤ x)
    (hupper : x ≤ 7 / 10) :
    11930 / 543 * x ^ 2 + 1611743 / 271500 ≤ 1193 / 50 * x := by
  have h := secant_le x (193 / 500) (7 / 10) hlower hupper (by norm_num)
  norm_num at h ⊢
  linarith

private theorem s0s3_high_radial_high_secant (x : ℝ) (hlower : 7 / 10 ≤ x)
    (hupper : x ≤ 1) :
    1193 / 85 * x ^ 2 + 8351 / 850 ≤ 1193 / 50 * x := by
  have h := secant_le x (7 / 10) 1 hlower hupper (by norm_num)
  norm_num at h ⊢
  linarith

private theorem s0s3_high_coefficient_le : 1193 / 50 ≤ 10 * (barC + 1) := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  linarith

private theorem s0s3_low_coefficient_le : 193 / 50 ≤ 10 * (barC - 1) := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  linarith

private theorem s0s3_low_low_constant_neg :
    815 / 12 + 1157 / 50 + 2 * (1263 / 50) - 2 * (871 / 100) * barC ^ 2 -
      2 * (37249 / 34650) - 2 * (1611743 / 271500) +
      54 * barC - 88 * barC ^ 2 < 0 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem s0s3_low_high_constant_neg :
    815 / 12 + 621 / 25 + 2701 / 100 + 1863 / 100 -
      (849 / 100 + 131 / 25) * barC ^ 2 - 2 * (37249 / 34650) -
      1611743 / 271500 - 8351 / 850 + 54 * barC - 88 * barC ^ 2 < 0 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem s0s3_high_high_constant_neg :
    815 / 12 + 2641 / 100 + 2 * (2071 / 100) - 2 * (517 / 100) * barC ^ 2 -
      2 * (37249 / 34650) - 2 * (8351 / 850) +
      54 * barC - 88 * barC ^ 2 < 0 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem s0s3_gramBound_low_low
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 11930 / 543 * (‖p₁‖ ^ 2 + ‖w₂‖ ^ 2) -
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      1157 / 50 + 2 * (1263 / 50) - 2 * (871 / 100) * barC ^ 2 := by
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w₁]
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hgram := s0s3_gram_low_low e p₁ p₂ w₁ w₂
  rw [he, one_pow] at hgram
  nlinarith only [hgram, hp₂Sq, hw₁Sq, hpsepSq, hwsepSq]

private theorem s0s3_gramBound_low_high
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 11930 / 543 * ‖p₁‖ ^ 2 -
        1193 / 85 * ‖w₂‖ ^ 2 - 1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      621 / 25 + 2701 / 100 + 1863 / 100 -
        (849 / 100 + 131 / 25) * barC ^ 2 := by
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w₁]
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hgram := s0s3_gram_low_high e p₁ p₂ w₁ w₂
  rw [he, one_pow] at hgram
  nlinarith only [hgram, hp₂Sq, hw₁Sq, hpsepSq, hwsepSq]

private theorem s0s3_gramBound_high_low
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 1193 / 85 * ‖p₁‖ ^ 2 -
        11930 / 543 * ‖w₂‖ ^ 2 - 1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      621 / 25 + 2701 / 100 + 1863 / 100 -
        (849 / 100 + 131 / 25) * barC ^ 2 := by
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w₁]
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hgram := s0s3_gram_high_low e p₁ p₂ w₁ w₂
  rw [he, one_pow] at hgram
  nlinarith only [hgram, hp₂Sq, hw₁Sq, hpsepSq, hwsepSq]

private theorem s0s3_gramBound_high_high
    (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 1193 / 85 * (‖p₁‖ ^ 2 + ‖w₂‖ ^ 2) -
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      2641 / 100 + 2 * (2071 / 100) - 2 * (517 / 100) * barC ^ 2 := by
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w₁]
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hgram := s0s3_gram_high_high e p₁ p₂ w₁ w₂
  rw [he, one_pow] at hgram
  nlinarith only [hgram, hp₂Sq, hw₁Sq, hpsepSq, hwsepSq]

omit [InnerProductSpace ℝ E] in
private theorem s0s3_radialBound_of_secants (p₁ p₂ w₁ w₂ : E)
    (pSlope pConstant wSlope wConstant : ℝ)
    (hp₁ : pSlope * ‖p₁‖ ^ 2 + pConstant ≤ 1193 / 50 * ‖p₁‖)
    (hp₂ : 1930 / 693 * ‖p₂‖ ^ 2 + 37249 / 34650 ≤ 193 / 50 * ‖p₂‖)
    (hw₁ : 1930 / 693 * ‖w₁‖ ^ 2 + 37249 / 34650 ≤ 193 / 50 * ‖w₁‖)
    (hw₂ : wSlope * ‖w₂‖ ^ 2 + wConstant ≤ 1193 / 50 * ‖w₂‖) :
    pSlope * ‖p₁‖ ^ 2 + wSlope * ‖w₂‖ ^ 2 +
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) +
        pConstant + wConstant + 2 * (37249 / 34650) ≤
      10 * (barC + 1) * (‖p₁‖ + ‖w₂‖) +
        10 * (barC - 1) * (‖p₂‖ + ‖w₁‖) := by
  have hhigh := mul_le_mul_of_nonneg_right s0s3_high_coefficient_le
    (add_nonneg (norm_nonneg p₁) (norm_nonneg w₂))
  have hlow := mul_le_mul_of_nonneg_right s0s3_low_coefficient_le
    (add_nonneg (norm_nonneg p₂) (norm_nonneg w₁))
  calc
    _ ≤ 1193 / 50 * (‖p₁‖ + ‖w₂‖) +
        193 / 50 * (‖p₂‖ + ‖w₁‖) := by linarith
    _ ≤ _ := add_le_add hhigh hlow

/-- A two-secant rational Gram separator for the `S0/S3` incidence representative. -/
theorem gramCertificate_s0s3 (e p₁ p₂ w₁ w₂ : E)
    (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    17 * ‖e - p₁ - w₁‖ + 20 * ‖e - p₂ - w₁‖ +
        17 * ‖e - p₂ - w₂‖ -
        10 * (barC + 1) * (‖p₁‖ + ‖w₂‖) -
        10 * (barC - 1) * (‖p₂‖ + ‖w₁‖) +
        54 * barC - 88 * barC ^ 2 < 0 := by
  have hp₁Lower := s0s3_radius_floor p₁ p₂ hp₂ hpsep
  have hp₂Lower := s0s3_radius_floor p₂ p₁ hp₁ (by simpa [norm_sub_rev] using hpsep)
  have hw₁Lower := s0s3_radius_floor w₁ w₂ hw₂ hwsep
  have hw₂Lower := s0s3_radius_floor w₂ w₁ hw₁ (by simpa [norm_sub_rev] using hwsep)
  have htangent := s0s3_positive_distances_le e p₁ p₂ w₁ w₂
  have hp₂Radial := s0s3_low_radial_secant ‖p₂‖ hp₂Lower hp₂
  have hw₁Radial := s0s3_low_radial_secant ‖w₁‖ hw₁Lower hw₁
  by_cases hp₁Low : ‖p₁‖ ≤ 7 / 10
  · have hp₁Radial := s0s3_high_radial_low_secant ‖p₁‖ hp₁Lower hp₁Low
    by_cases hw₂Low : ‖w₂‖ ≤ 7 / 10
    · have hw₂Radial := s0s3_high_radial_low_secant ‖w₂‖ hw₂Lower hw₂Low
      have hgram :=
        s0s3_gramBound_low_low e p₁ p₂ w₁ w₂ he hp₂ hw₁ hpsep hwsep
      have hradial := s0s3_radialBound_of_secants p₁ p₂ w₁ w₂
        (11930 / 543) (1611743 / 271500) (11930 / 543) (1611743 / 271500)
        hp₁Radial hp₂Radial hw₁Radial hw₂Radial
      nlinarith only [htangent, hgram, hradial, s0s3_low_low_constant_neg]
    · have hw₂Radial := s0s3_high_radial_high_secant ‖w₂‖
        (le_of_not_ge hw₂Low) hw₂
      have hgram :=
        s0s3_gramBound_low_high e p₁ p₂ w₁ w₂ he hp₂ hw₁ hpsep hwsep
      have hradial := s0s3_radialBound_of_secants p₁ p₂ w₁ w₂
        (11930 / 543) (1611743 / 271500) (1193 / 85) (8351 / 850)
        hp₁Radial hp₂Radial hw₁Radial hw₂Radial
      nlinarith only [htangent, hgram, hradial, s0s3_low_high_constant_neg]
  · have hp₁Radial := s0s3_high_radial_high_secant ‖p₁‖
      (le_of_not_ge hp₁Low) hp₁
    by_cases hw₂Low : ‖w₂‖ ≤ 7 / 10
    · have hw₂Radial := s0s3_high_radial_low_secant ‖w₂‖ hw₂Lower hw₂Low
      have hgram :=
        s0s3_gramBound_high_low e p₁ p₂ w₁ w₂ he hp₂ hw₁ hpsep hwsep
      have hradial := s0s3_radialBound_of_secants p₁ p₂ w₁ w₂
        (1193 / 85) (8351 / 850) (11930 / 543) (1611743 / 271500)
        hp₁Radial hp₂Radial hw₁Radial hw₂Radial
      nlinarith only [htangent, hgram, hradial, s0s3_low_high_constant_neg]
    · have hw₂Radial := s0s3_high_radial_high_secant ‖w₂‖
        (le_of_not_ge hw₂Low) hw₂
      have hgram :=
        s0s3_gramBound_high_high e p₁ p₂ w₁ w₂ he hp₂ hw₁ hpsep hwsep
      have hradial := s0s3_radialBound_of_secants p₁ p₂ w₁ w₂
        (1193 / 85) (8351 / 850) (1193 / 85) (8351 / 850)
        hp₁Radial hp₂Radial hw₁Radial hw₂Radial
      nlinarith only [htangent, hgram, hradial, s0s3_high_high_constant_neg]

/-- The `S0/S3` separator is strictly negative for every admissible configuration. -/
theorem balancedBalancedS0S3GramBound_of_admissible
    {configuration : SixPointConfiguration E} (h : configuration.IsAdmissibleAt barS) :
    7 * diagonalMatchingReducedSlack configuration +
        20 * redBalancedReducedSlack configuration 0 +
        20 * blueBalancedReducedSlack configuration 3 < 0 := by
  let e := configuration.rootDisplacement
  let p₁ := configuration.redDisplacement .left
  let p₂ := configuration.redDisplacement .right
  let w₁ := configuration.bluePullback .left
  let w₂ := configuration.bluePullback .right
  have hpsep : barC ≤ ‖p₁ - p₂‖ := by
    have hred := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hred
    exact hred
  have hwsep : barC ≤ ‖w₁ - w₂‖ := by
    have hblue := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hblue
    exact hblue
  have hcertificate := gramCertificate_s0s3 e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp)) hpsep hwsep
  simp only [diagonalMatchingReducedSlack, redBalancedReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm]
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild]
  dsimp only [e, p₁, p₂, w₁, w₂] at hcertificate
  nlinarith

/-- The `S0/S3` balanced/balanced representative is impossible. -/
theorem not_redBalanced_zero_and_blueBalanced_three
    {configuration : SixPointConfiguration E} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 3)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redBalancedReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 3 hblue
  have hbound := balancedBalancedS0S3GramBound_of_admissible h
  nlinarith

end Besicovitch
