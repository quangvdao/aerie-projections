/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Arithmetic.Interval.Reflection
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Regimes.Dense.ScalarInterpolation
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.LobeTail
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum

/-!
# Low-mass diffuse threshold scalar envelope

This module starts the diffuse threshold slice where the normalized squared
mass `x = V / b²` lies in `[1, 11/10]`.  At the lower Hölder exponent
`p = (32/9) x` and threshold-normalized tilt `s = (33/10) x`, the quotient
`s / p` is the constant `297/320`.  Thus the moving endpoint is bounded by
one fixed Gaussian integral.  A two-even-moment majorant gives the strict
kernel-checked bound `481/1000`.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections
namespace ThresholdDiffuseLowScalar

private lemma gaussian_cos_power_integrable (t : ℝ) (n : ℕ) :
    Integrable (fun G : ℝ => Real.cos (t * G) ^ n)
      (gaussianReal 0 1) := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [] with G
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)

def precision : ℕ := 48
def squarings : ℕ := 32

/-- Certify a rational upper bound on `exp (-x)` from the reflected interval
checker used by diffuse scalar profiles. -/
theorem exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck
      (Exp.negUpper precision x squarings) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  have hcontains := Exp.negUpper_contains
    (p := precision) (k := squarings) (x := x) hx
  exact Interval.lt_of_contains_of_upperLTCheck hcontains hcheck

/-! A small variable-scale even-moment producer.  Keeping this local avoids
depending on the much heavier Hermite certificate merely to evaluate the
three endpoints `4, 6, 8`. -/

private noncomputable def evenCosineFourier (n : ℕ) (t G : ℝ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) / 2 ^ (2 * n) +
    ∑ j ∈ Finset.range n,
      (Nat.choose (2 * n) (n - (j + 1)) : ℝ) / 2 ^ (2 * n - 1) *
        Real.cos (((2 * (j + 1) : ℕ) : ℝ) * t * G)

private lemma evenCosineFourier_integrable (n : ℕ) (t : ℝ) :
    Integrable (evenCosineFourier n t) (gaussianReal 0 1) := by
  apply Integrable.add
  · fun_prop
  · apply MeasureTheory.integrable_finsetSum
    intro j hj
    have hc := gaussian_cos_integrable (2 * ((j : ℝ) + 1) * t)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      hc.const_mul
        ((Nat.choose (2 * n) (n - (j + 1)) : ℝ) / 2 ^ (2 * n - 1))

private theorem gaussian_integral_evenCosineFourier (n : ℕ) (t : ℝ) :
    (∫ G : ℝ, evenCosineFourier n t G ∂(gaussianReal 0 1)) =
      (Nat.choose (2 * n) n : ℝ) / 2 ^ (2 * n) +
        ∑ j ∈ Finset.range n,
          (Nat.choose (2 * n) (n - (j + 1)) : ℝ) / 2 ^ (2 * n - 1) *
            Real.exp (-((((2 * (j + 1) : ℕ) : ℝ) * t) ^ 2) / 2) := by
  rw [show evenCosineFourier n t = fun G =>
      (Nat.choose (2 * n) n : ℝ) / 2 ^ (2 * n) +
        ∑ j ∈ Finset.range n,
          (Nat.choose (2 * n) (n - (j + 1)) : ℝ) / 2 ^ (2 * n - 1) *
            Real.cos (((2 * (j + 1) : ℕ) : ℝ) * t * G) by rfl]
  rw [integral_add]
  · rw [integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, add_right_inj]
    rw [MeasureTheory.integral_finsetSum (Finset.range n) (by
      intro j hj
      have hc := gaussian_cos_integrable (2 * ((j : ℝ) + 1) * t)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
        hc.const_mul
          ((Nat.choose (2 * n) (n - (j + 1)) : ℝ) / 2 ^ (2 * n - 1)))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, gaussian_cosine_charFun]
  · fun_prop
  · apply MeasureTheory.integrable_finsetSum
    intro j hj
    have hc := gaussian_cos_integrable (2 * ((j : ℝ) + 1) * t)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      hc.const_mul
        ((Nat.choose (2 * n) (n - (j + 1)) : ℝ) / 2 ^ (2 * n - 1))

private theorem gaussian_even_cosine_moment
    (n : ℕ) (s p : ℝ) (hsp : 0 ≤ s / p)
    (hFourier : ∀ z : ℝ,
      Real.cos z ^ (2 * n) = evenCosineFourier n 1 z) :
    (∫ G : ℝ, Real.cos (Real.sqrt (s / p) * G) ^ (2 * n)
        ∂(gaussianReal 0 1)) =
      (Nat.choose (2 * n) n : ℝ) / 2 ^ (2 * n) +
        ∑ j ∈ Finset.range n,
          (Nat.choose (2 * n) (n - (j + 1)) : ℝ) / 2 ^ (2 * n - 1) *
            Real.exp (-2 * ((j + 1 : ℕ) : ℝ) ^ 2 * (s / p)) := by
  let t := Real.sqrt (s / p)
  have ht : t ^ 2 = s / p := Real.sq_sqrt hsp
  calc
    (∫ G : ℝ, Real.cos (Real.sqrt (s / p) * G) ^ (2 * n)
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ, evenCosineFourier n t G ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      rw [hFourier (t * G)]
      simp only [evenCosineFourier]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      apply congrArg Real.cos
      push_cast
      ring
    _ = _ := by
      rw [gaussian_integral_evenCosineFourier]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      calc
        -(((2 * (j + 1) : ℕ) : ℝ) * t) ^ 2 / 2 =
            -2 * ((j + 1 : ℕ) : ℝ) ^ 2 * t ^ 2 := by
          push_cast
          ring
        _ = _ := by rw [ht]

private theorem abs_pow_two_mul (z : ℝ) (n : ℕ) :
    |z| ^ (2 * n) = z ^ (2 * n) := by
  rw [← abs_pow, abs_of_nonneg ((even_two_mul n).pow_nonneg z)]

private theorem sparseScalarF_even_eq_integral (n : ℕ) (s : ℝ) :
    sparseScalarF s ((2 * n : ℕ) : ℝ) =
      ∫ G : ℝ,
        Real.cos (Real.sqrt (s / ((2 * n : ℕ) : ℝ)) * G) ^ (2 * n)
        ∂(gaussianReal 0 1) := by
  unfold sparseScalarF
  apply integral_congr_ae
  filter_upwards [] with G
  dsimp [sparseScalarFIntegrand]
  rw [Real.rpow_natCast, abs_pow_two_mul]

private theorem evenFourier_four (z : ℝ) :
    Real.cos z ^ (2 * 2) = evenCosineFourier 2 1 z := by
  rw [← abs_pow_two_mul (Real.cos z) 2, DenseScalar.cos_four_identity]
  norm_num [evenCosineFourier, Finset.sum_range_succ, Nat.choose]
  ring

private theorem evenFourier_two (z : ℝ) :
    Real.cos z ^ (2 * 1) = evenCosineFourier 1 1 z := by
  rw [← abs_pow_two_mul (Real.cos z) 1, DenseScalar.cos_two_identity]
  norm_num [evenCosineFourier, Finset.sum_range_succ, Nat.choose]

private theorem evenFourier_six (z : ℝ) :
    Real.cos z ^ (2 * 3) = evenCosineFourier 3 1 z := by
  rw [← abs_pow_two_mul (Real.cos z) 3, DenseScalar.cos_six_identity]
  norm_num [evenCosineFourier, Finset.sum_range_succ, Nat.choose]
  ring

private theorem evenFourier_eight (z : ℝ) :
    Real.cos z ^ (2 * 4) = evenCosineFourier 4 1 z := by
  rw [← abs_pow_two_mul (Real.cos z) 4, DenseScalar.cos_eight_identity]
  norm_num [evenCosineFourier, Finset.sum_range_succ, Nat.choose]
  ring

/-- Exact four-moment formula for the sparse scalar envelope. -/
theorem sparseScalarF_four_exact {s : ℝ} (hs : 0 ≤ s) :
    sparseScalarF s 4 =
      (3 / 8 : ℝ) + (1 / 2 : ℝ) * Real.exp (-s / 2) +
        (1 / 8 : ℝ) * Real.exp (-2 * s) := by
  have heq := sparseScalarF_even_eq_integral 2 s
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at heq
  rw [heq]
  rw [gaussian_even_cosine_moment 2 s 4 (by positivity) evenFourier_four]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring_nf

/-- Exact six-moment formula for the sparse scalar envelope. -/
theorem sparseScalarF_six_exact {s : ℝ} (hs : 0 ≤ s) :
    sparseScalarF s 6 =
      (10 / 32 : ℝ) + (15 / 32 : ℝ) * Real.exp (-s / 3) +
        (6 / 32 : ℝ) * Real.exp (-4 * s / 3) +
          (1 / 32 : ℝ) * Real.exp (-3 * s) := by
  have heq := sparseScalarF_even_eq_integral 3 s
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at heq
  rw [heq]
  rw [gaussian_even_cosine_moment 3 s 6 (by positivity) evenFourier_six]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring_nf

/-- Exact eight-moment formula for the sparse scalar envelope. -/
theorem sparseScalarF_eight_exact {s : ℝ} (hs : 0 ≤ s) :
    sparseScalarF s 8 =
      (35 / 128 : ℝ) + (56 / 128 : ℝ) * Real.exp (-s / 4) +
        (28 / 128 : ℝ) * Real.exp (-s) +
          (8 / 128 : ℝ) * Real.exp (-9 * s / 4) +
            (1 / 128 : ℝ) * Real.exp (-4 * s) := by
  have heq := sparseScalarF_even_eq_integral 4 s
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at heq
  rw [heq]
  rw [gaussian_even_cosine_moment 4 s 8 (by positivity) evenFourier_eight]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring_nf

private theorem fixedScaleMomentTwo :
    (∫ G : ℝ, Real.cos (Real.sqrt (297 / 320 : ℝ) * G) ^ 2
        ∂(gaussianReal 0 1)) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.exp (-(297 / 160 : ℝ)) := by
  have h := gaussian_even_cosine_moment 1 (297 / 320) 1
    (by norm_num) evenFourier_two
  norm_num [Finset.sum_range_succ, Nat.choose] at h ⊢
  convert h using 1 <;> ring

private theorem fixedScaleMomentFour :
    (∫ G : ℝ, Real.cos (Real.sqrt (297 / 320 : ℝ) * G) ^ 4
        ∂(gaussianReal 0 1)) =
      (3 / 8 : ℝ) + (1 / 2 : ℝ) * Real.exp (-(297 / 160 : ℝ)) +
        (1 / 8 : ℝ) * Real.exp (-(297 / 40 : ℝ)) := by
  have h := gaussian_even_cosine_moment 2 (297 / 320) 1
    (by norm_num) evenFourier_four
  norm_num [Finset.sum_range_succ, Nat.choose] at h ⊢
  convert h using 1 <;> ring

private theorem fixedEndpoint_pointwise (G : ℝ) :
    sparseScalarFIntegrand (33 / 10) (32 / 9) G ≤
      (2 / 9 : ℝ) *
          Real.cos (Real.sqrt (297 / 320 : ℝ) * G) ^ 2 +
        (7 / 9 : ℝ) *
          Real.cos (Real.sqrt (297 / 320 : ℝ) * G) ^ 4 := by
  let t : ℝ := |Real.cos (Real.sqrt (297 / 320 : ℝ) * G)|
  have ht : 0 ≤ t := abs_nonneg _
  have hgm := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := (2 / 9 : ℝ)) (w₂ := (7 / 9 : ℝ))
    (p₁ := t ^ 2) (p₂ := t ^ 4)
    (by norm_num) (by norm_num) (sq_nonneg t) (by positivity)
    (by norm_num)
  have hlhs :
      (t ^ 2 : ℝ) ^ (2 / 9 : ℝ) *
          (t ^ 4 : ℝ) ^ (7 / 9 : ℝ) =
        t ^ (32 / 9 : ℝ) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_natCast t 4,
      ← Real.rpow_mul ht, ← Real.rpow_mul ht,
      ← Real.rpow_add_of_nonneg ht (by norm_num) (by norm_num)]
    congr 1
    norm_num
  dsimp [sparseScalarFIntegrand]
  rw [show (33 / 10 : ℝ) / (32 / 9) = 297 / 320 by norm_num]
  rw [← hlhs]
  have habs4 (z : ℝ) : |z| ^ 4 = z ^ 4 := by
    calc
      |z| ^ 4 = (|z| ^ 2) ^ 2 := by ring
      _ = (z ^ 2) ^ 2 := by rw [sq_abs]
      _ = z ^ 4 := by ring
  simpa only [t, sq_abs, habs4] using hgm

set_option maxHeartbeats 800000 in
-- The integral normalizer elaborates two nested Fourier decompositions.
private theorem fixedEndpoint_le_expression :
    sparseScalarF (33 / 10) (32 / 9) ≤
      (29 / 72 : ℝ) +
        (1 / 2 : ℝ) * Real.exp (-(297 / 160 : ℝ)) +
          (7 / 72 : ℝ) * Real.exp (-(297 / 40 : ℝ)) := by
  let t : ℝ := Real.sqrt (297 / 320 : ℝ)
  have ht : t ^ 2 = (297 / 320 : ℝ) := by
    dsimp [t]
    exact Real.sq_sqrt (by norm_num)
  have hleft := sparseScalarF_integrable
    (s := (33 / 10 : ℝ)) (p := (32 / 9 : ℝ)) (by norm_num)
  have h2 := gaussian_cos_power_integrable t 2
  have h4 := gaussian_cos_power_integrable t 4
  have hright : Integrable (fun G : ℝ =>
      (2 / 9 : ℝ) * Real.cos (t * G) ^ 2 +
        (7 / 9 : ℝ) * Real.cos (t * G) ^ 4)
      (gaussianReal 0 1) :=
    (h2.const_mul (2 / 9 : ℝ)).add (h4.const_mul (7 / 9 : ℝ))
  have hmono := integral_mono_ae hleft hright
    (Filter.Eventually.of_forall fixedEndpoint_pointwise)
  have hm2 :
      (∫ G : ℝ, Real.cos (t * G) ^ 2 ∂(gaussianReal 0 1)) =
        (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) := by
    have hpoint (G : ℝ) :
        Real.cos (t * G) ^ 2 =
          (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) := by
      simpa [sq_abs, mul_assoc] using DenseScalar.cos_two_identity (t * G)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_add (integrable_const _)
        ((gaussian_cos_integrable (2 * t)).const_mul _),
      integral_const, integral_const_mul, gaussian_cosine_charFun]
    simp
  have hm4 :
      (∫ G : ℝ, Real.cos (t * G) ^ 4 ∂(gaussianReal 0 1)) =
        (3 / 8 : ℝ) + (1 / 2 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (1 / 8 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) := by
    have hpoint (G : ℝ) :
        Real.cos (t * G) ^ 4 =
          (3 / 8 : ℝ) + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
            (1 / 8 : ℝ) * Real.cos ((4 * t) * G) := by
      calc
        Real.cos (t * G) ^ 4 = |Real.cos (t * G)| ^ 4 := by
          rw [show Real.cos (t * G) ^ 4 =
                (Real.cos (t * G) ^ 2) ^ 2 by ring,
            show |Real.cos (t * G)| ^ 4 =
                (|Real.cos (t * G)| ^ 2) ^ 2 by ring,
            sq_abs]
        _ = _ := by
          simpa [mul_assoc] using DenseScalar.cos_four_identity (t * G)
    have h0 : Integrable (fun _ : ℝ => (3 / 8 : ℝ))
        (gaussianReal 0 1) := integrable_const _
    have h2i : Integrable (fun G : ℝ =>
        (1 / 2 : ℝ) * Real.cos ((2 * t) * G))
        (gaussianReal 0 1) :=
      (gaussian_cos_integrable (2 * t)).const_mul _
    have h4i : Integrable (fun G : ℝ =>
        (1 / 8 : ℝ) * Real.cos ((4 * t) * G))
        (gaussianReal 0 1) :=
      (gaussian_cos_integrable (4 * t)).const_mul _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    calc
      (∫ G : ℝ,
          (3 / 8 : ℝ) + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
            (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
          ∂(gaussianReal 0 1)) =
          (∫ G : ℝ,
            (3 / 8 : ℝ) + (1 / 2 : ℝ) * Real.cos ((2 * t) * G)
            ∂(gaussianReal 0 1)) +
          ∫ G : ℝ, (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
            ∂(gaussianReal 0 1) := by
        have h := integral_add (μ := gaussianReal 0 1) (h0.add h2i) h4i
        simpa only [Pi.add_apply] using h
      _ = ((∫ G : ℝ, (3 / 8 : ℝ) ∂(gaussianReal 0 1)) +
            ∫ G : ℝ, (1 / 2 : ℝ) * Real.cos ((2 * t) * G)
              ∂(gaussianReal 0 1)) +
          ∫ G : ℝ, (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
            ∂(gaussianReal 0 1) := by
        have h := integral_add (μ := gaussianReal 0 1) h0 h2i
        simpa only [Pi.add_apply] using congrArg
          (fun z => z + ∫ G : ℝ,
            (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1)) h
      _ = (3 / 8 : ℝ) + (1 / 2 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (1 / 8 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) := by
        rw [integral_const_mul, integral_const_mul, integral_const,
          gaussian_cosine_charFun, gaussian_cosine_charFun]
        simp
  unfold sparseScalarF at hmono ⊢
  calc
    (∫ G : ℝ, sparseScalarFIntegrand (33 / 10) (32 / 9) G
        ∂(gaussianReal 0 1)) ≤
        ∫ G : ℝ,
          (2 / 9 : ℝ) * Real.cos (t * G) ^ 2 +
            (7 / 9 : ℝ) * Real.cos (t * G) ^ 4
          ∂(gaussianReal 0 1) := hmono
    _ = (2 / 9 : ℝ) *
          (∫ G : ℝ, Real.cos (t * G) ^ 2 ∂(gaussianReal 0 1)) +
        (7 / 9 : ℝ) *
          (∫ G : ℝ, Real.cos (t * G) ^ 4 ∂(gaussianReal 0 1)) := by
      rw [integral_add (h2.const_mul _) (h4.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = (2 / 9 : ℝ) *
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) *
            Real.exp (-(2 * t) ^ 2 / 2)) +
        (7 / 9 : ℝ) *
          ((3 / 8 : ℝ) + (1 / 2 : ℝ) *
              Real.exp (-(2 * t) ^ 2 / 2) +
            (1 / 8 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2)) := by
      rw [hm2, hm4]
    _ = (29 / 72 : ℝ) +
        (1 / 2 : ℝ) * Real.exp (-(297 / 160 : ℝ)) +
          (7 / 72 : ℝ) * Real.exp (-(297 / 40 : ℝ)) := by
      rw [show -(2 * t) ^ 2 / 2 = -(297 / 160 : ℝ) by nlinarith [ht],
        show -(4 * t) ^ 2 / 2 = -(297 / 40 : ℝ) by nlinarith [ht]]
      ring

private theorem fixedEndpoint_expression_lt :
    (29 / 72 : ℝ) +
        (1 / 2 : ℝ) * Real.exp (-(297 / 160 : ℝ)) +
          (7 / 72 : ℝ) * Real.exp (-(297 / 40 : ℝ)) <
      (481 / 1000 : ℝ) := by
  have h1 := exp_neg_lt (x := (297 / 160 : ℚ))
    (u := (1563 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (297 / 40 : ℚ))
    (u := (61 / 100000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

/-- The fixed lower endpoint is strictly below the `0.481` scalar cap. -/
theorem sparseScalarF_fixedEndpoint_lt :
    sparseScalarF (33 / 10) (32 / 9) < (481 / 1000 : ℝ) :=
  fixedEndpoint_le_expression.trans_lt fixedEndpoint_expression_lt

private theorem highEndpoint_pointwise (G : ℝ) :
    sparseScalarFIntegrand (429 / 125) (832 / 225) G ≤
      (34 / 225 : ℝ) *
          Real.cos (Real.sqrt (297 / 320 : ℝ) * G) ^ 2 +
        (191 / 225 : ℝ) *
          Real.cos (Real.sqrt (297 / 320 : ℝ) * G) ^ 4 := by
  let t : ℝ := |Real.cos (Real.sqrt (297 / 320 : ℝ) * G)|
  have ht : 0 ≤ t := abs_nonneg _
  have hgm := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := (34 / 225 : ℝ)) (w₂ := (191 / 225 : ℝ))
    (p₁ := t ^ 2) (p₂ := t ^ 4)
    (by norm_num) (by norm_num) (sq_nonneg t) (by positivity)
    (by norm_num)
  have hlhs :
      (t ^ 2 : ℝ) ^ (34 / 225 : ℝ) *
          (t ^ 4 : ℝ) ^ (191 / 225 : ℝ) =
        t ^ (832 / 225 : ℝ) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_natCast t 4,
      ← Real.rpow_mul ht, ← Real.rpow_mul ht,
      ← Real.rpow_add_of_nonneg ht (by norm_num) (by norm_num)]
    congr 1
    norm_num
  dsimp [sparseScalarFIntegrand]
  rw [show (429 / 125 : ℝ) / (832 / 225) = 297 / 320 by norm_num]
  rw [← hlhs]
  have habs4 (z : ℝ) : |z| ^ 4 = z ^ 4 := by
    calc
      |z| ^ 4 = (|z| ^ 2) ^ 2 := by ring
      _ = (z ^ 2) ^ 2 := by rw [sq_abs]
      _ = z ^ 4 := by ring
  simpa only [t, sq_abs, habs4] using hgm

private theorem highEndpoint_le_expression :
    sparseScalarF (429 / 125) (832 / 225) ≤
      (709 / 1800 : ℝ) +
        (1 / 2 : ℝ) * Real.exp (-(297 / 160 : ℝ)) +
          (191 / 1800 : ℝ) * Real.exp (-(297 / 40 : ℝ)) := by
  let t : ℝ := Real.sqrt (297 / 320 : ℝ)
  have h2 := gaussian_cos_power_integrable t 2
  have h4 := gaussian_cos_power_integrable t 4
  have hleft := sparseScalarF_integrable
    (s := (429 / 125 : ℝ)) (p := (832 / 225 : ℝ)) (by norm_num)
  have hright : Integrable (fun G : ℝ =>
      (34 / 225 : ℝ) * Real.cos (t * G) ^ 2 +
        (191 / 225 : ℝ) * Real.cos (t * G) ^ 4)
      (gaussianReal 0 1) :=
    (h2.const_mul _).add (h4.const_mul _)
  have hmono := integral_mono_ae hleft hright
    (Filter.Eventually.of_forall highEndpoint_pointwise)
  unfold sparseScalarF at hmono ⊢
  calc
    (∫ G : ℝ, sparseScalarFIntegrand (429 / 125) (832 / 225) G
        ∂(gaussianReal 0 1)) ≤
        ∫ G : ℝ,
          (34 / 225 : ℝ) * Real.cos (t * G) ^ 2 +
            (191 / 225 : ℝ) * Real.cos (t * G) ^ 4
          ∂(gaussianReal 0 1) := hmono
    _ = (34 / 225 : ℝ) *
          (∫ G : ℝ, Real.cos (t * G) ^ 2 ∂(gaussianReal 0 1)) +
        (191 / 225 : ℝ) *
          (∫ G : ℝ, Real.cos (t * G) ^ 4 ∂(gaussianReal 0 1)) := by
      rw [integral_add (h2.const_mul _) (h4.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = (709 / 1800 : ℝ) +
        (1 / 2 : ℝ) * Real.exp (-(297 / 160 : ℝ)) +
          (191 / 1800 : ℝ) * Real.exp (-(297 / 40 : ℝ)) := by
      dsimp [t]
      rw [fixedScaleMomentTwo, fixedScaleMomentFour]
      ring

private theorem highEndpoint_expression_lt :
    (709 / 1800 : ℝ) +
        (1 / 2 : ℝ) * Real.exp (-(297 / 160 : ℝ)) +
          (191 / 1800 : ℝ) * Real.exp (-(297 / 40 : ℝ)) <
      (473 / 1000 : ℝ) := by
  have h1 := exp_neg_lt (x := (297 / 160 : ℚ))
    (u := (1563 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (297 / 40 : ℚ))
    (u := (61 / 100000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

private theorem sparseScalarF_highEndpoint_lt :
    sparseScalarF (429 / 125) (832 / 225) < (473 / 1000 : ℝ) :=
  highEndpoint_le_expression.trans_lt highEndpoint_expression_lt

/-- Above the `26/25` split, the moving lower endpoint is below `0.473`. -/
theorem sparseScalarF_movingEndpoint_high_lt {x : ℝ}
    (hx : (26 / 25 : ℝ) ≤ x) :
    sparseScalarF ((33 / 10) * x) ((32 / 9) * x) <
      (473 / 1000 : ℝ) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hratio :
      ((33 / 10 : ℝ) * x) / ((32 / 9 : ℝ) * x) = 297 / 320 := by
    field_simp [hxpos.ne']
    ring
  have hfixed : (429 / 125 : ℝ) / (832 / 225) = 297 / 320 := by norm_num
  have hpoint (G : ℝ) :
      sparseScalarFIntegrand ((33 / 10) * x) ((32 / 9) * x) G ≤
        sparseScalarFIntegrand (429 / 125) (832 / 225) G := by
    dsimp [sparseScalarFIntegrand]
    rw [hratio, hfixed]
    apply Real.rpow_le_rpow_of_exponent_ge'
    · exact abs_nonneg _
    · exact Real.abs_cos_le_one _
    · norm_num
    · nlinarith
  have hle :
      sparseScalarF ((33 / 10) * x) ((32 / 9) * x) ≤
        sparseScalarF (429 / 125) (832 / 225) := by
    unfold sparseScalarF
    exact integral_mono_ae
      (sparseScalarF_integrable (by positivity))
      (sparseScalarF_integrable (by norm_num))
      (Filter.Eventually.of_forall hpoint)
  exact hle.trans_lt sparseScalarF_highEndpoint_lt

/-- Along the lower coupled exponent, the cosine scale is constant and the
larger normalized mass only raises a base in `[0,1]` to a larger power. -/
theorem sparseScalarF_movingEndpoint_le {x : ℝ} (hx : 1 ≤ x) :
    sparseScalarF ((33 / 10) * x) ((32 / 9) * x) ≤
      sparseScalarF (33 / 10) (32 / 9) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hratio :
      ((33 / 10 : ℝ) * x) / ((32 / 9 : ℝ) * x) = 297 / 320 := by
    field_simp [hxpos.ne']
    ring
  have hfixed : (33 / 10 : ℝ) / (32 / 9) = 297 / 320 := by norm_num
  have hpoint (G : ℝ) :
      sparseScalarFIntegrand ((33 / 10) * x) ((32 / 9) * x) G ≤
        sparseScalarFIntegrand (33 / 10) (32 / 9) G := by
    dsimp [sparseScalarFIntegrand]
    rw [hratio, hfixed]
    apply Real.rpow_le_rpow_of_exponent_ge'
    · exact abs_nonneg _
    · exact Real.abs_cos_le_one _
    · norm_num
    · nlinarith
  unfold sparseScalarF
  exact integral_mono_ae
    (sparseScalarF_integrable (by positivity))
    (sparseScalarF_integrable (by norm_num))
    (Filter.Eventually.of_forall hpoint)

/-- The moving lower endpoint inherits the strict `0.481` certificate. -/
theorem sparseScalarF_movingEndpoint_lt {x : ℝ} (hx : 1 ≤ x) :
    sparseScalarF ((33 / 10) * x) ((32 / 9) * x) <
      (481 / 1000 : ℝ) :=
  (sparseScalarF_movingEndpoint_le hx).trans_lt sparseScalarF_fixedEndpoint_lt

/-- Uniform fourth-moment endpoint for every tilt in the low-mass slice. -/
theorem sparseScalarF_four_lt {s : ℝ} (hs : (33 / 10 : ℝ) ≤ s) :
    sparseScalarF s 4 < (472 / 1000 : ℝ) := by
  rw [sparseScalarF_four_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 2) ≤ Real.exp (-(33 / 20 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-2 * s) ≤ Real.exp (-(33 / 5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (33 / 20 : ℚ))
    (u := (193 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (33 / 5 : ℚ))
    (u := (2 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

/-- Uniform sixth-moment endpoint for every tilt in the low-mass slice. -/
theorem sparseScalarF_six_lt {s : ℝ} (hs : (33 / 10 : ℝ) ≤ s) :
    sparseScalarF s 6 < (472 / 1000 : ℝ) := by
  rw [sparseScalarF_six_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 3) ≤ Real.exp (-(11 / 10 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-4 * s / 3) ≤ Real.exp (-(22 / 5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9mono : Real.exp (-3 * s) ≤ Real.exp (-(99 / 10 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (11 / 10 : ℚ))
    (u := (333 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (22 / 5 : ℚ))
    (u := (13 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h9 := exp_neg_lt (x := (99 / 10 : ℚ))
    (u := (1 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

/-- Uniform eighth-moment endpoint for every tilt in the low-mass slice. -/
theorem sparseScalarF_eight_lt {s : ℝ} (hs : (33 / 10 : ℝ) ≤ s) :
    sparseScalarF s 8 < (474 / 1000 : ℝ) := by
  rw [sparseScalarF_eight_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 4) ≤ Real.exp (-(33 / 40 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-s) ≤ Real.exp (-(33 / 10 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9mono : Real.exp (-9 * s / 4) ≤ Real.exp (-(297 / 40 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h16mono : Real.exp (-4 * s) ≤ Real.exp (-(66 / 5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (33 / 40 : ℚ))
    (u := (439 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (33 / 10 : ℚ))
    (u := (37 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h9 := exp_neg_lt (x := (297 / 40 : ℚ))
    (u := (61 / 100000 : ℚ)) (by norm_num) (by decide +kernel)
  have h16 := exp_neg_lt (x := (66 / 5 : ℚ))
    (u := (1 / 100000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

/-- Stronger fourth-moment endpoint above the `26/25` mass split. -/
theorem sparseScalarF_four_high_lt {s : ℝ}
    (hs : (429 / 125 : ℝ) ≤ s) :
    sparseScalarF s 4 < (466 / 1000 : ℝ) := by
  rw [sparseScalarF_four_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 2) ≤ Real.exp (-(429 / 250 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-2 * s) ≤ Real.exp (-(858 / 125 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (429 / 250 : ℚ))
    (u := (18 / 100 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (858 / 125 : ℚ))
    (u := (11 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

/-- Stronger sixth-moment endpoint above the `26/25` mass split. -/
theorem sparseScalarF_six_high_lt {s : ℝ}
    (hs : (429 / 125 : ℝ) ≤ s) :
    sparseScalarF s 6 < (466 / 1000 : ℝ) := by
  rw [sparseScalarF_six_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 3) ≤ Real.exp (-(143 / 125 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-4 * s / 3) ≤ Real.exp (-(572 / 125 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9mono : Real.exp (-3 * s) ≤ Real.exp (-(1287 / 125 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (143 / 125 : ℚ))
    (u := (319 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (572 / 125 : ℚ))
    (u := (103 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  have h9 := exp_neg_lt (x := (1287 / 125 : ℚ))
    (u := (4 / 100000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

/-- Stronger eighth-moment endpoint above the `26/25` mass split. -/
theorem sparseScalarF_eight_high_lt {s : ℝ}
    (hs : (429 / 125 : ℝ) ≤ s) :
    sparseScalarF s 8 < (467 / 1000 : ℝ) := by
  rw [sparseScalarF_eight_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 4) ≤ Real.exp (-(429 / 500 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-s) ≤ Real.exp (-(429 / 125 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9mono : Real.exp (-9 * s / 4) ≤ Real.exp (-(3861 / 500 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h16mono : Real.exp (-4 * s) ≤ Real.exp (-(1716 / 125 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (429 / 500 : ℚ))
    (u := (425 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (429 / 125 : ℚ))
    (u := (33 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h9 := exp_neg_lt (x := (3861 / 500 : ℚ))
    (u := (45 / 100000 : ℚ)) (by norm_num) (by decide +kernel)
  have h16 := exp_neg_lt (x := (1716 / 125 : ℚ))
    (u := (2 / 1000000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

private theorem scalar_lt_of_harmonic_caps
    {F L H M D C : ℝ}
    (hbound : F ≤ L * Real.sqrt H)
    (hL0 : 0 ≤ L) (hLM : L ≤ M) (hH0 : 0 ≤ H) (hHD : H ≤ D)
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C) (hgap : M ^ 2 * D < C ^ 2) :
    F < C := by
  have hsqrt0 : 0 ≤ Real.sqrt H := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt H) ^ 2 = H := Real.sq_sqrt hH0
  have hleft0 : 0 ≤ L * Real.sqrt H := mul_nonneg hL0 hsqrt0
  have hright0 : 0 ≤ M * Real.sqrt H := mul_nonneg hM0 hsqrt0
  have hleftRight : L * Real.sqrt H ≤ M * Real.sqrt H :=
    mul_le_mul_of_nonneg_right hLM hsqrt0
  have hsquares : (L * Real.sqrt H) ^ 2 ≤ (M * Real.sqrt H) ^ 2 := by
    nlinarith
  have hrightSquare : (M * Real.sqrt H) ^ 2 ≤ M ^ 2 * D := by
    rw [mul_pow, hsqrtSq]
    exact mul_le_mul_of_nonneg_left hHD (sq_nonneg M)
  have hstrict : L * Real.sqrt H < C := by
    nlinarith
  exact hbound.trans_lt hstrict

private theorem theta_mul_one_sub_le_quarter {theta : ℝ}
    (_h0 : 0 ≤ theta) (_h1 : theta ≤ 1) :
    theta * (1 - theta) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (theta - 1 / 2)]

/-- Harmonic interpolation from a moving endpoint in `[32/9, 4]` to `4`
costs at most the factor `289/288`. -/
theorem variable_harmonic_le {a p theta : ℝ}
    (ha0 : (32 / 9 : ℝ) ≤ a) (ha1 : a ≤ 4)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hp : p = (1 - theta) * a + theta * 4) :
    p * ((1 - theta) / a + theta / 4) ≤ (289 / 288 : ℝ) := by
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha0
  have htheta0 : 0 ≤ theta * (1 - theta) := mul_nonneg h0 (sub_nonneg.mpr h1)
  have htheta := theta_mul_one_sub_le_quarter h0 h1
  have hcoeff0 : 0 ≤ (4 - a) ^ 2 / (4 * a) := by positivity
  have hcoeff : (4 - a) ^ 2 / (4 * a) ≤ (1 / 72 : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * a)]
    nlinarith [sq_nonneg (a - 32 / 9)]
  have hproduct :
      (4 - a) ^ 2 / (4 * a) * (theta * (1 - theta)) ≤
        (1 / 72 : ℝ) * (1 / 4) := by
    exact mul_le_mul hcoeff htheta htheta0 (by norm_num)
  have hid :
      p * ((1 - theta) / a + theta / 4) =
        1 + (4 - a) ^ 2 / (4 * a) * (theta * (1 - theta)) := by
    rw [hp]
    field_simp [hapos.ne']
    ring
  rw [hid]
  norm_num at hproduct ⊢
  linarith

/-- Harmonic interpolation between `4` and `6` costs at most `25/24`. -/
theorem four_six_harmonic_le {p theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hp : p = (1 - theta) * 4 + theta * 6) :
    p * ((1 - theta) / 4 + theta / 6) ≤ (25 / 24 : ℝ) := by
  have htheta := theta_mul_one_sub_le_quarter h0 h1
  rw [hp]
  have hid :
      ((1 - theta) * 4 + theta * 6) *
          ((1 - theta) / 4 + theta / 6) =
        1 + (1 / 6 : ℝ) * (theta * (1 - theta)) := by ring
  rw [hid]
  nlinarith

/-- Harmonic interpolation between `6` and `8` costs at most `49/48`. -/
theorem six_eight_harmonic_le {p theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hp : p = (1 - theta) * 6 + theta * 8) :
    p * ((1 - theta) / 6 + theta / 8) ≤ (49 / 48 : ℝ) := by
  have htheta := theta_mul_one_sub_le_quarter h0 h1
  rw [hp]
  have hid :
      ((1 - theta) * 6 + theta * 8) *
          ((1 - theta) / 6 + theta / 8) =
        1 + (1 / 12 : ℝ) * (theta * (1 - theta)) := by ring
  rw [hid]
  nlinarith

/-- Turn endpoint scalar bounds and a harmonic interpolation cap into a strict
bound throughout one interpolation segment. -/
theorem interpolation_segment_lt
    {s a b p theta A B M D C : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hp0 : 0 < p) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hp : p = (1 - theta) * a + theta * b)
    (hFa : sparseScalarF s a ≤ A) (hFb : sparseScalarF s b ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hAM : A ≤ M) (hBM : B ≤ M)
    (hH0 : 0 ≤ p * ((1 - theta) / a + theta / b))
    (hHD : p * ((1 - theta) / a + theta / b) ≤ D)
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C) (hgap : M ^ 2 * D < C ^ 2) :
    sparseScalarF s p < C := by
  have hbound := DenseScalar.sparseScalarF_mul_sqrt_harmonic_le
    hs ha hb hab hp0 htheta0 htheta1 hp hFa hFb hA0 hB0
  apply scalar_lt_of_harmonic_caps hbound
  · positivity
  · calc
      (1 - theta) * A + theta * B ≤
          (1 - theta) * M + theta * M :=
        add_le_add
          (mul_le_mul_of_nonneg_left hAM (sub_nonneg.mpr htheta1))
          (mul_le_mul_of_nonneg_left hBM htheta0)
      _ = M := by ring
  · exact hH0
  · exact hHD
  · exact hM0
  · exact hC0
  · exact hgap

/-- On the lower mass band, harmonic interpolation between the moving
endpoint and the even endpoints `4, 6, 8` stays below `0.4824`. -/
theorem sparseScalarF_lowBand_to_eight_lt {x p : ℝ}
    (hx0 : 1 ≤ x) (hx1 : x ≤ 26 / 25)
    (hp0 : (32 / 9) * x ≤ p) (hp1 : p ≤ 8) :
    sparseScalarF ((33 / 10) * x) p < (603 / 1250 : ℝ) := by
  let s : ℝ := (33 / 10) * x
  let a : ℝ := (32 / 9) * x
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx0
  have hs : 0 < s := by dsimp [s]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : (32 / 9 : ℝ) ≤ a := by dsimp [a]; nlinarith
  have ha4 : a < 4 := by dsimp [a]; norm_num at hx1 ⊢; nlinarith
  have hp_pos : 0 < p := lt_of_lt_of_le ha hp0
  have hs_base : (33 / 10 : ℝ) ≤ s := by dsimp [s]; nlinarith
  have hFa : sparseScalarF s a ≤ (481 / 1000 : ℝ) := by
    dsimp [s, a]
    exact le_of_lt (sparseScalarF_movingEndpoint_lt hx0)
  by_cases hp4 : p ≤ 4
  · let theta : ℝ := (p - a) / (4 - a)
    have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
    have htheta1 : theta ≤ 1 := by
      dsimp [theta]
      rw [div_le_one (sub_pos.mpr ha4)]
      linarith
    have hp : p = (1 - theta) * a + theta * 4 := by
      dsimp [theta]
      field_simp [ne_of_gt (sub_pos.mpr ha4)]
      ring
    have hH0 : 0 ≤ p * ((1 - theta) / a + theta / 4) := by positivity
    have hHD := variable_harmonic_le ha0 ha4.le htheta0 htheta1 hp
    exact interpolation_segment_lt (M := (481 / 1000 : ℝ))
      (D := (289 / 288 : ℝ)) (C := (603 / 1250 : ℝ))
      hs ha (by norm_num) ha4 hp_pos htheta0 htheta1 hp
      hFa (le_of_lt (sparseScalarF_four_lt hs_base)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hH0 hHD (by norm_num) (by norm_num) (by norm_num)
  · have hp4' : 4 ≤ p := le_of_not_ge hp4
    by_cases hp6 : p ≤ 6
    · let theta : ℝ := (p - 4) / 2
      have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
      have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
      have hp : p = (1 - theta) * 4 + theta * 6 := by dsimp [theta]; ring
      have hH0 : 0 ≤ p * ((1 - theta) / 4 + theta / 6) := by positivity
      have hHD := four_six_harmonic_le htheta0 htheta1 hp
      exact interpolation_segment_lt (M := (472 / 1000 : ℝ))
        (D := (25 / 24 : ℝ)) (C := (603 / 1250 : ℝ))
        hs (by norm_num) (by norm_num) (by norm_num)
        hp_pos htheta0 htheta1 hp
        (le_of_lt (sparseScalarF_four_lt hs_base))
        (le_of_lt (sparseScalarF_six_lt hs_base))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hH0 hHD (by norm_num) (by norm_num) (by norm_num)
    · have hp6' : 6 ≤ p := le_of_not_ge hp6
      let theta : ℝ := (p - 6) / 2
      have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
      have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
      have hp : p = (1 - theta) * 6 + theta * 8 := by dsimp [theta]; ring
      have hH0 : 0 ≤ p * ((1 - theta) / 6 + theta / 8) := by positivity
      have hHD := six_eight_harmonic_le htheta0 htheta1 hp
      exact interpolation_segment_lt (M := (474 / 1000 : ℝ))
        (D := (49 / 48 : ℝ)) (C := (603 / 1250 : ℝ))
        hs (by norm_num) (by norm_num) (by norm_num)
        hp_pos htheta0 htheta1 hp
        (le_of_lt (sparseScalarF_six_lt hs_base))
        (le_of_lt (sparseScalarF_eight_lt hs_base))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hH0 hHD (by norm_num) (by norm_num) (by norm_num)

/-- Above the `26/25` mass split, the stronger moving and even endpoints
give the round scalar cap `0.48` through exponent eight. -/
theorem sparseScalarF_highBand_to_eight_lt {x p : ℝ}
    (hx0 : (26 / 25 : ℝ) ≤ x) (hx1 : x ≤ 11 / 10)
    (hp0 : (32 / 9) * x ≤ p) (hp1 : p ≤ 8) :
    sparseScalarF ((33 / 10) * x) p < (12 / 25 : ℝ) := by
  let s : ℝ := (33 / 10) * x
  let a : ℝ := (32 / 9) * x
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx0
  have hs : 0 < s := by dsimp [s]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : (32 / 9 : ℝ) ≤ a := by dsimp [a]; nlinarith
  have ha4 : a < 4 := by dsimp [a]; norm_num at hx1 ⊢; nlinarith
  have hp_pos : 0 < p := lt_of_lt_of_le ha hp0
  have hs_high : (429 / 125 : ℝ) ≤ s := by dsimp [s]; nlinarith
  have hFa : sparseScalarF s a ≤ (473 / 1000 : ℝ) := by
    dsimp [s, a]
    exact le_of_lt (sparseScalarF_movingEndpoint_high_lt hx0)
  by_cases hp4 : p ≤ 4
  · let theta : ℝ := (p - a) / (4 - a)
    have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
    have htheta1 : theta ≤ 1 := by
      dsimp [theta]
      rw [div_le_one (sub_pos.mpr ha4)]
      linarith
    have hp : p = (1 - theta) * a + theta * 4 := by
      dsimp [theta]
      field_simp [ne_of_gt (sub_pos.mpr ha4)]
      ring
    have hH0 : 0 ≤ p * ((1 - theta) / a + theta / 4) := by positivity
    have hHD := variable_harmonic_le ha0 ha4.le htheta0 htheta1 hp
    exact interpolation_segment_lt (M := (473 / 1000 : ℝ))
      (D := (289 / 288 : ℝ)) (C := (12 / 25 : ℝ))
      hs ha (by norm_num) ha4 hp_pos htheta0 htheta1 hp
      hFa (le_of_lt (sparseScalarF_four_high_lt hs_high)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hH0 hHD (by norm_num) (by norm_num) (by norm_num)
  · have hp4' : 4 ≤ p := le_of_not_ge hp4
    by_cases hp6 : p ≤ 6
    · let theta : ℝ := (p - 4) / 2
      have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
      have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
      have hp : p = (1 - theta) * 4 + theta * 6 := by dsimp [theta]; ring
      have hH0 : 0 ≤ p * ((1 - theta) / 4 + theta / 6) := by positivity
      have hHD := four_six_harmonic_le htheta0 htheta1 hp
      exact interpolation_segment_lt (M := (466 / 1000 : ℝ))
        (D := (25 / 24 : ℝ)) (C := (12 / 25 : ℝ))
        hs (by norm_num) (by norm_num) (by norm_num)
        hp_pos htheta0 htheta1 hp
        (le_of_lt (sparseScalarF_four_high_lt hs_high))
        (le_of_lt (sparseScalarF_six_high_lt hs_high))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hH0 hHD (by norm_num) (by norm_num) (by norm_num)
    · have hp6' : 6 ≤ p := le_of_not_ge hp6
      let theta : ℝ := (p - 6) / 2
      have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
      have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
      have hp : p = (1 - theta) * 6 + theta * 8 := by dsimp [theta]; ring
      have hH0 : 0 ≤ p * ((1 - theta) / 6 + theta / 8) := by positivity
      have hHD := six_eight_harmonic_le htheta0 htheta1 hp
      exact interpolation_segment_lt (M := (467 / 1000 : ℝ))
        (D := (49 / 48 : ℝ)) (C := (12 / 25 : ℝ))
        hs (by norm_num) (by norm_num) (by norm_num)
        hp_pos htheta0 htheta1 hp
        (le_of_lt (sparseScalarF_six_high_lt hs_high))
        (le_of_lt (sparseScalarF_eight_high_lt hs_high))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hH0 hHD (by norm_num) (by norm_num) (by norm_num)

/-- A rational lower bound on `π²` used by diffuse lobe estimates. -/
theorem pi_sq_gt_986_over_100 :
    (986 / 100 : ℝ) < Real.pi ^ 2 := by
  nlinarith [Real.pi_gt_d4, Real.pi_pos]

private theorem lowBand_lobe_cap_lt :
    1 / Real.sqrt (1 + (33 / 10 : ℝ)) *
        (1 + 2 * Real.exp
            (-((1000 / 429 : ℝ) * (33 / 10) * Real.pi ^ 2 /
              (2 * (1 + (33 / 10))))) /
          (1 - (Real.exp
            (-((1000 / 429 : ℝ) * (33 / 10) * Real.pi ^ 2 /
              (2 * (1 + (33 / 10)))))) ^ 3)) <
      (603 / 1250 : ℝ) := by
  let c : ℝ := (1000 / 429 : ℝ) * (33 / 10) * Real.pi ^ 2 /
    (2 * (1 + (33 / 10)))
  let y : ℝ := Real.exp (-c)
  have hc : (4930 / 559 : ℝ) < c := by
    calc
      (4930 / 559 : ℝ) = (500 / 559) * (986 / 100) := by norm_num
      _ < (500 / 559) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left pi_sq_gt_986_over_100 (by norm_num)
      _ = c := by dsimp [c]; ring
  have hy : y < (3 / 20000 : ℝ) := by
    have hmono : y < Real.exp (-(4930 / 559 : ℝ)) := by
      dsimp [y]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hcert : Real.exp (-(4930 / 559 : ℝ)) < (3 / 20000 : ℝ) := by
      convert exp_neg_lt (x := (4930 / 559 : ℚ))
        (u := (3 / 20000 : ℚ)) (by norm_num) (by decide +kernel) using 1 <;> norm_num
    exact hmono.trans hcert
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy3 : y ^ 3 < (3 / 20000 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hy hy0 (by norm_num)
  have hden : 0 < 1 - y ^ 3 := by nlinarith
  have htail :
      2 * y / (1 - y ^ 3) <
        2 * (3 / 20000 : ℝ) / (1 - (3 / 20000 : ℝ) ^ 3) := by
    rw [div_lt_div_iff₀ hden (by norm_num)]
    nlinarith
  have hsqrt : (4000 / 1929 : ℝ) < Real.sqrt (1 + (33 / 10 : ℝ)) := by
    have hsqrt0 := Real.sqrt_nonneg (1 + (33 / 10 : ℝ))
    have hsqrtSq := Real.sq_sqrt
      (by norm_num : (0 : ℝ) ≤ 1 + (33 / 10 : ℝ))
    nlinarith
  have hinv : 1 / Real.sqrt (1 + (33 / 10 : ℝ)) < (1929 / 4000 : ℝ) := by
    have hsqrtPos : 0 < Real.sqrt (1 + (33 / 10 : ℝ)) := by positivity
    apply (div_lt_iff₀ hsqrtPos).2
    nlinarith
  have hfactor : 0 < 1 + 2 * y / (1 - y ^ 3) := by positivity
  calc
    1 / Real.sqrt (1 + (33 / 10 : ℝ)) *
        (1 + 2 * Real.exp
          (-((1000 / 429 : ℝ) * (33 / 10) * Real.pi ^ 2 /
            (2 * (1 + (33 / 10))))) /
          (1 - (Real.exp
            (-((1000 / 429 : ℝ) * (33 / 10) * Real.pi ^ 2 /
              (2 * (1 + (33 / 10)))))) ^ 3)) =
        1 / Real.sqrt (1 + (33 / 10 : ℝ)) *
          (1 + 2 * y / (1 - y ^ 3)) := by rfl
    _ < (1929 / 4000 : ℝ) * (1 + 2 * y / (1 - y ^ 3)) :=
      mul_lt_mul_of_pos_right hinv hfactor
    _ < (1929 / 4000 : ℝ) *
        (1 + 2 * (3 / 20000 : ℝ) /
          (1 - (3 / 20000 : ℝ) ^ 3)) := by
      exact mul_lt_mul_of_pos_left (by linarith) (by norm_num)
    _ < (603 / 1250 : ℝ) := by norm_num

private theorem highBand_lobe_cap_lt :
    1 / Real.sqrt (1 + (429 / 125 : ℝ)) *
        (1 + 2 * Real.exp
            (-((800 / 363 : ℝ) * (429 / 125) * Real.pi ^ 2 /
              (2 * (1 + (429 / 125))))) /
          (1 - (Real.exp
            (-((800 / 363 : ℝ) * (429 / 125) * Real.pi ^ 2 /
              (2 * (1 + (429 / 125)))))) ^ 3)) <
      (12 / 25 : ℝ) := by
  let c : ℝ := (800 / 363 : ℝ) * (429 / 125) * Real.pi ^ 2 /
    (2 * (1 + (429 / 125)))
  let y : ℝ := Real.exp (-c)
  have hc : (25636 / 3047 : ℝ) < c := by
    calc
      (25636 / 3047 : ℝ) = (2600 / 3047) * (986 / 100) := by norm_num
      _ < (2600 / 3047) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left pi_sq_gt_986_over_100 (by norm_num)
      _ = c := by dsimp [c]; ring
  have hy : y < (1 / 4000 : ℝ) := by
    have hmono : y < Real.exp (-(25636 / 3047 : ℝ)) := by
      dsimp [y]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hcert : Real.exp (-(25636 / 3047 : ℝ)) < (1 / 4000 : ℝ) := by
      convert exp_neg_lt (x := (25636 / 3047 : ℚ))
        (u := (1 / 4000 : ℚ)) (by norm_num) (by decide +kernel) using 1 <;> norm_num
    exact hmono.trans hcert
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy3 : y ^ 3 < (1 / 4000 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hy hy0 (by norm_num)
  have hden : 0 < 1 - y ^ 3 := by nlinarith
  have htail :
      2 * y / (1 - y ^ 3) <
        2 * (1 / 4000 : ℝ) / (1 - (1 / 4000 : ℝ) ^ 3) := by
    rw [div_lt_div_iff₀ hden (by norm_num)]
    nlinarith
  have hsqrt : (10000 / 4751 : ℝ) < Real.sqrt (1 + (429 / 125 : ℝ)) := by
    have hsqrt0 := Real.sqrt_nonneg (1 + (429 / 125 : ℝ))
    have hsqrtSq := Real.sq_sqrt
      (by norm_num : (0 : ℝ) ≤ 1 + (429 / 125 : ℝ))
    nlinarith
  have hinv : 1 / Real.sqrt (1 + (429 / 125 : ℝ)) < (4751 / 10000 : ℝ) := by
    have hsqrtPos : 0 < Real.sqrt (1 + (429 / 125 : ℝ)) := by positivity
    apply (div_lt_iff₀ hsqrtPos).2
    nlinarith
  have hfactor : 0 < 1 + 2 * y / (1 - y ^ 3) := by positivity
  calc
    1 / Real.sqrt (1 + (429 / 125 : ℝ)) *
        (1 + 2 * Real.exp
          (-((800 / 363 : ℝ) * (429 / 125) * Real.pi ^ 2 /
            (2 * (1 + (429 / 125))))) /
          (1 - (Real.exp
            (-((800 / 363 : ℝ) * (429 / 125) * Real.pi ^ 2 /
              (2 * (1 + (429 / 125)))))) ^ 3)) =
        1 / Real.sqrt (1 + (429 / 125 : ℝ)) *
          (1 + 2 * y / (1 - y ^ 3)) := by rfl
    _ < (4751 / 10000 : ℝ) * (1 + 2 * y / (1 - y ^ 3)) :=
      mul_lt_mul_of_pos_right hinv hfactor
    _ < (4751 / 10000 : ℝ) *
        (1 + 2 * (1 / 4000 : ℝ) /
          (1 - (1 / 4000 : ℝ) ^ 3)) := by
      exact mul_lt_mul_of_pos_left (by linarith) (by norm_num)
    _ < (12 / 25 : ℝ) := by norm_num

/-- The complete low normalized-mass scalar band, including all exponents
above eight. -/
theorem sparseScalarF_lowBand_lt {x p : ℝ}
    (hx0 : 1 ≤ x) (hx1 : x ≤ 26 / 25)
    (hp0 : (32 / 9) * x ≤ p) :
    sparseScalarF ((33 / 10) * x) p < (603 / 1250 : ℝ) := by
  by_cases hp8 : p ≤ 8
  · exact sparseScalarF_lowBand_to_eight_lt hx0 hx1 hp0 hp8
  · have hp8' : 8 ≤ p := le_of_not_ge hp8
    have hs : (33 / 10 : ℝ) ≤ (33 / 10) * x := by nlinarith
    have hratio :
        (1000 / 429 : ℝ) * ((33 / 10) * x) ≤ p := by
      have : (1000 / 429 : ℝ) * ((33 / 10) * x) ≤ 8 := by
        norm_num at hx1 ⊢
        nlinarith
      exact this.trans hp8'
    exact (sparseScalarF_lobe_periodization_of_tilt_ratio
      (s := (33 / 10 : ℝ) * x) (p := p)
      (sLower := (33 / 10 : ℝ)) (r := (1000 / 429 : ℝ))
      (by norm_num) hs (by norm_num) hratio).trans_lt lowBand_lobe_cap_lt

/-- The complete upper normalized-mass scalar band, including all exponents
above eight. -/
theorem sparseScalarF_highBand_lt {x p : ℝ}
    (hx0 : (26 / 25 : ℝ) ≤ x) (hx1 : x ≤ 11 / 10)
    (hp0 : (32 / 9) * x ≤ p) :
    sparseScalarF ((33 / 10) * x) p < (12 / 25 : ℝ) := by
  by_cases hp8 : p ≤ 8
  · exact sparseScalarF_highBand_to_eight_lt hx0 hx1 hp0 hp8
  · have hp8' : 8 ≤ p := le_of_not_ge hp8
    have hs : (429 / 125 : ℝ) ≤ (33 / 10) * x := by nlinarith
    have hratio :
        (800 / 363 : ℝ) * ((33 / 10) * x) ≤ p := by
      have : (800 / 363 : ℝ) * ((33 / 10) * x) ≤ 8 := by
        norm_num at hx1 ⊢
        nlinarith
      exact this.trans hp8'
    exact (sparseScalarF_lobe_periodization_of_tilt_ratio
      (s := (33 / 10 : ℝ) * x) (p := p)
      (sLower := (429 / 125 : ℝ)) (r := (800 / 363 : ℝ))
      (by norm_num) hs (by norm_num) hratio).trans_lt highBand_lobe_cap_lt

/-! ## Reusable two/four moment interpolation

The interpolation controls moving endpoints between exponents two and four
without introducing a new numerical oracle. -/

private theorem gaussian_moment_two_at (r : ℝ) (hr : 0 ≤ r) :
    (∫ G : ℝ, Real.cos (Real.sqrt r * G) ^ 2 ∂(gaussianReal 0 1)) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.exp (-2 * r) := by
  have h := gaussian_even_cosine_moment 1 r 1 (by simpa using hr) evenFourier_two
  norm_num [Finset.sum_range_succ, Nat.choose] at h ⊢
  exact h

private theorem gaussian_moment_four_at (r : ℝ) (hr : 0 ≤ r) :
    (∫ G : ℝ, Real.cos (Real.sqrt r * G) ^ 4 ∂(gaussianReal 0 1)) =
      (3 / 8 : ℝ) + (1 / 2 : ℝ) * Real.exp (-2 * r) +
        (1 / 8 : ℝ) * Real.exp (-8 * r) := by
  have h := gaussian_even_cosine_moment 2 r 1 (by simpa using hr) evenFourier_four
  norm_num [Finset.sum_range_succ, Nat.choose] at h ⊢
  convert h using 1
  ring

set_option maxHeartbeats 800000 in
-- Weighted real-power normalization and Gaussian integration are intensive.
/-- Bound the sparse scalar envelope between exponents two and four by the
corresponding convex combination of exact Gaussian moments. -/
theorem sparseScalarF_between_two_four_le
    {s p r : ℝ} (hp2 : 2 ≤ p) (hp4 : p ≤ 4) (hr : 0 ≤ r)
    (hsp : s / p = r) :
    sparseScalarF s p ≤
      ((4 - p) / 2) *
          ((1 / 2 : ℝ) + (1 / 2) * Real.exp (-2 * r)) +
        ((p - 2) / 2) *
          ((3 / 8 : ℝ) + (1 / 2) * Real.exp (-2 * r) +
            (1 / 8) * Real.exp (-8 * r)) := by
  let t : ℝ := Real.sqrt r
  let w₂ : ℝ := (4 - p) / 2
  let w₄ : ℝ := (p - 2) / 2
  have hw₂ : 0 ≤ w₂ := by dsimp [w₂]; linarith
  have hw₄ : 0 ≤ w₄ := by dsimp [w₄]; linarith
  have hsum : w₂ + w₄ = 1 := by dsimp [w₂, w₄]; ring
  have hexponent : 2 * w₂ + 4 * w₄ = p := by dsimp [w₂, w₄]; ring
  have hpoint (G : ℝ) :
      sparseScalarFIntegrand s p G ≤
        w₂ * Real.cos (t * G) ^ 2 + w₄ * Real.cos (t * G) ^ 4 := by
    let z : ℝ := |Real.cos (t * G)|
    have hz : 0 ≤ z := abs_nonneg _
    have hgm := Real.geom_mean_le_arith_mean2_weighted
      (w₁ := w₂) (w₂ := w₄) (p₁ := z ^ 2) (p₂ := z ^ 4)
      hw₂ hw₄ (sq_nonneg z) (by positivity) hsum
    have hlhs : (z ^ 2 : ℝ) ^ w₂ * (z ^ 4 : ℝ) ^ w₄ = z ^ p := by
      rw [← Real.rpow_natCast z 2, ← Real.rpow_natCast z 4,
        ← Real.rpow_mul hz, ← Real.rpow_mul hz,
        ← Real.rpow_add_of_nonneg hz (by positivity) (by positivity)]
      norm_num only [Nat.cast_ofNat]
      rw [hexponent]
    dsimp [sparseScalarFIntegrand]
    rw [hsp]
    rw [← hlhs]
    have habs4 (a : ℝ) : |a| ^ 4 = a ^ 4 := by
      calc
        |a| ^ 4 = (|a| ^ 2) ^ 2 := by ring
        _ = (a ^ 2) ^ 2 := by rw [sq_abs]
        _ = a ^ 4 := by ring
    simpa only [z, t, sq_abs, habs4] using hgm
  have hleft := sparseScalarF_integrable (s := s) (p := p) (lt_of_lt_of_le (by norm_num) hp2)
  have h2 := gaussian_cos_power_integrable t 2
  have h4 := gaussian_cos_power_integrable t 4
  have hmono := integral_mono_ae hleft
    ((h2.const_mul w₂).add (h4.const_mul w₄))
    (Filter.Eventually.of_forall hpoint)
  unfold sparseScalarF at hmono ⊢
  calc
    _ ≤ ∫ G : ℝ, w₂ * Real.cos (t * G) ^ 2 +
        w₄ * Real.cos (t * G) ^ 4 ∂(gaussianReal 0 1) := hmono
    _ = w₂ * (∫ G : ℝ, Real.cos (t * G) ^ 2 ∂(gaussianReal 0 1)) +
        w₄ * (∫ G : ℝ, Real.cos (t * G) ^ 4 ∂(gaussianReal 0 1)) := by
      rw [integral_add (h2.const_mul _) (h4.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = _ := by
      dsimp [t]
      rw [gaussian_moment_two_at r hr, gaussian_moment_four_at r hr]

end ThresholdDiffuseLowScalar
end CertifiedProjections
