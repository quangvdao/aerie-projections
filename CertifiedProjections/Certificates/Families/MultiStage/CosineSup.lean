/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.EntryLaw
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.MomentCore
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.CosineMGF
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Regimes.Diffuse.LowScalar
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.LobeTail
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# MGF constant of the ternary entry law

The main result is `EntryLaw.ternary_mgfConstant`: the ternary entry law satisfies
`MGFConstant 3 (21 / 40)`. It rests on `cosineMoment_three_le`, which bounds
`gaussianCosineMoment 3 (2 / w)` by `262447 / 500000` for every `0 < w ≤ 1`. Here
`gaussianCosineMoment s p` is the expectation of `|cos (√(s / p) * G)| ^ p` for a standard Gaussian
`G`, and `sparseScalarF s p` is the same quantity as a real number.

Spec Lemma C and Lemmas C.1–C.3.

For exponents `p` between two and four, the bound on the cosine moment follows from a convex
combination of the second and fourth cosine moments. For larger exponents it follows from
`sparseScalarF_lobe_periodization`, which bounds the cosine moment by a sum of Gaussian terms
indexed by the integers. Finite Taylor sums certify the rational bounds on the exponential. The
one-row MGF estimate then follows by the generalized Hölder inequality.
-/

open scoped BigOperators ENNReal NNReal

open Set

namespace CertifiedProjections.MultiStage

/-- `exp (-3)` is at most `24894 / 500000`. -/
private lemma exp_neg_three_le : Real.exp (-3) ≤ (24894 / 500000 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 16
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  nlinarith

/-- `exp (-6)` is at most `1 / 100`. -/
private lemma exp_neg_six_le : Real.exp (-6) ≤ (1 / 100 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  nlinarith

/-- For `x ≥ 0`, `(5 / 3) * x ^ 2 ≤ exp x`. -/
private lemma exp_quadratic_lower (x : ℝ) (hx : 0 ≤ x) :
    (5 / 3 : ℝ) * x ^ 2 ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x / 2 - 1)
  have hsq : (x / 2) ^ 2 ≤ Real.exp (x / 2 - 1) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have heq : Real.exp (x / 2 - 1) ^ 2 = Real.exp x / Real.exp 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    ring
  rw [heq] at hsq
  have hmul := (le_div_iff₀ (Real.exp_pos 2)).1 hsq
  have htwo := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at htwo
  nlinarith [sq_nonneg x]

/-- For `p > 0`, the quantity `exp (-6 / p) * (6 / p ^ 2)`, which is the derivative of
`exp (-6 / p)` in `p`, is at most `1 / 10`. -/
private lemma exp_recip_deriv_bound (p : ℝ) (hp : 0 < p) :
    Real.exp (-6 / p) * (6 / p ^ 2) ≤ (1 / 10 : ℝ) := by
  have h := exp_quadratic_lower (6 / p) (by positivity)
  have hmul : (5 / 3 : ℝ) * (6 / p) ^ 2 * Real.exp (-6 / p) ≤ 1 := by
    calc
      _ ≤ Real.exp (6 / p) * Real.exp (-6 / p) :=
        mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
  field_simp at hmul ⊢
  nlinarith

/-- For `p ≥ 2`, `exp (-6 / p) ≤ exp (-3) + (p - 2) / 10`. -/
private lemma exp_recip_linear (p : ℝ) (hp : 2 ≤ p) :
    Real.exp (-6 / p) ≤ Real.exp (-3) + (p - 2) / 10 := by
  let f : ℝ → ℝ := fun x => Real.exp (-6 / x)
  let f' : ℝ → ℝ := fun x => Real.exp (-6 / x) * (6 / x ^ 2)
  have hd (x : ℝ) (hx : 2 ≤ x) : HasDerivAt f (f' x) x := by
    have hx0 : x ≠ 0 := by linarith
    convert ((hasDerivAt_const x (-6)).div (hasDerivAt_id x) hx0).exp using 1 <;>
      dsimp [f, f']; ring
  have hbound := image_le_of_deriv_right_le_deriv_boundary
    (f := f) (f' := f') (a := 2) (b := p)
    (B := fun x => Real.exp (-3) + (x - 2) / 10) (B' := fun _ => 1 / 10)
    (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
    (fun x hx => (hd x hx.1).hasDerivWithinAt)
    (by norm_num [f])
    (by fun_prop)
    (fun x _ => by
      convert (((hasDerivAt_id x).sub_const 2).div_const 10).const_add
        (Real.exp (-3)) |>.hasDerivWithinAt using 1 <;> norm_num <;> rfl)
    (fun x hx => exp_recip_deriv_bound x (by linarith [hx.1]))
  exact hbound ⟨hp, le_rfl⟩

/-- For `2 ≤ p ≤ 4`, `sparseScalarF 3 p` is at most `262447 / 500000`. -/
private lemma sparseScalarF_three_le_of_le_four (p : ℝ) (hp : 2 ≤ p) (hp4 : p ≤ 4) :
    sparseScalarF 3 p ≤ (262447 / 500000 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have h := ThresholdDiffuseLowScalar.sparseScalarF_between_two_four_le
    (s := 3) (p := p) (r := 3 / p) hp hp4 (by positivity) rfl
  have h6 := exp_recip_linear p hp
  have h24 : Real.exp (-8 * (3 / p)) ≤ (1 / 100 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) exp_neg_six_le
    have : (-8 : ℝ) * (3 / p) = -24 / p := by ring
    rw [this]
    exact (div_le_iff₀ hp0).2 (by linarith)
  have heq : -2 * (3 / p) = -6 / p := by ring
  rw [heq] at h
  have h24mul := mul_le_mul_of_nonneg_left h24 (show 0 ≤ (p - 2) / 16 by linarith)
  have h3 := exp_neg_three_le
  nlinarith

/-- `exp (-(9 / 2))` is at most `1 / 50`. -/
private theorem exp_neg_nine_halves_le : Real.exp (-(9 / 2 : ℝ)) ≤ 1 / 50 := by
  have h := Real.sum_le_exp_of_nonneg (x := (9 / 2 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg]
  simpa only [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 50) (by linarith : 50 ≤ Real.exp (9 / 2 : ℝ))

/-- For `p ≥ 4`, `sparseScalarF 3 p` is at most `262447 / 500000`. -/
private theorem sparseScalarF_three_le_of_four_le {p : ℝ} (hp : 4 ≤ p) :
    sparseScalarF 3 p ≤ (262447 / 500000 : ℝ) := by
  have hp_pos : 0 < p := by linarith
  have hL := sparseScalarF_lobe_periodization (s := (3 : ℝ)) (by norm_num) hp_pos
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcoeff : (9 / 2 : ℝ) ≤ p * Real.pi ^ 2 / 8 := by
    have hsq : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
    have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg Real.pi)
    nlinarith
  have hterm (k : ℤ) :
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + (3 : ℝ)))) ≤
        Real.exp (-(9 / 2 : ℝ) * (k : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (k : ℝ))
    calc
      -(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + (3 : ℝ))) =
          -(p * Real.pi ^ 2 / 8 * (k : ℝ) ^ 2) := by ring
      _ ≤ -(9 / 2 : ℝ) * (k : ℝ) ^ 2 := by nlinarith
  have ht := summable_real_integer_exp_neg_sq (c := (9 / 2 : ℝ)) (by norm_num)
  have hs := ht.of_nonneg_of_le (fun _ => Real.exp_nonneg _) hterm
  have hsum := (hs.tsum_le_tsum hterm ht).trans
    (scalarLobe_real_integer_exp_geometricTail (c := (9 / 2 : ℝ)) (by norm_num))
  have hρ := exp_neg_nine_halves_le
  have hρ0 := Real.exp_pos (-(9 / 2 : ℝ))
  have hcube : Real.exp (-(9 / 2 : ℝ)) ^ 3 ≤ (1 / 50 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hρ0.le hρ 3
  have hden : 0 < 1 - Real.exp (-(9 / 2 : ℝ)) ^ 3 := by nlinarith
  have hquot : 2 * Real.exp (-(9 / 2 : ℝ)) /
      (1 - Real.exp (-(9 / 2 : ℝ)) ^ 3) ≤ (24894 / 500000 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hsqrt : Real.sqrt (1 + (3 : ℝ)) = 2 := by
    rw [show 1 + (3 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsqrt] at hL
  calc
    sparseScalarF 3 p ≤ 1 / 2 *
        (1 + 2 * Real.exp (-(9 / 2 : ℝ)) /
          (1 - Real.exp (-(9 / 2 : ℝ)) ^ 3)) :=
      hL.trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2))
    _ ≤ (262447 / 500000 : ℝ) := by linarith

/-- Spec Lemmas C.1–C.3: the uniform bound on `h₃(w)`. For every `0 < w ≤ 1`,
`gaussianCosineMoment 3 (2 / w)` is at most `262447 / 500000`. -/
theorem cosineMoment_three_le (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    gaussianCosineMoment 3 (2 / w) ≤ ENNReal.ofReal (262447 / 500000) := by
  have hp : 2 ≤ 2 / w := (le_div_iff₀ hw).2 (by linarith)
  rw [gaussianCosineMoment_eq_ofReal_sparseScalarF (by positivity : 0 < 2 / w)]
  apply ENNReal.ofReal_le_ofReal
  by_cases hp4 : 2 / w ≤ 4
  · exact sparseScalarF_three_le_of_le_four (2 / w) hp hp4
  · exact sparseScalarF_three_le_of_four_le (le_of_not_ge hp4)

/-- Spec Lemma C: the MGF constant of the ternary entry law. The ternary entry law satisfies
`MGFConstant` with `t = 3` and `K = 21 / 40`. -/
theorem EntryLaw.ternary_mgfConstant : EntryLaw.ternary.MGFConstant 3 (21 / 40) := by
  classical
  intro f u hu
  let S : Finset (Fin f) := Finset.univ.filter (fun i => u i ≠ 0)
  have hS : ∀ i, i ∈ S ↔ u i ≠ 0 := by simp [S]
  have hsum : ∑ i ∈ S, u i ^ 2 = 1 := by
    calc
      ∑ i ∈ S, u i ^ 2 = ∑ i, u i ^ 2 := by
        apply Finset.sum_subset (by simp)
        intro i hi hnot
        have hz : u i = 0 := by simpa [S] using hnot
        simp [hz]
      _ = 1 := hu
  have hweight (i : Fin f) : u i ^ 2 ≤ 1 := by
    calc
      u i ^ 2 ≤ ∑ j, u j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
      _ = 1 := hu
  have hexp : MeasureTheory.Integrable
      (fun a => Real.exp (-3 * realRowDot a u ^ 2)) (sparseRademacherRow f).toMeasure := by
    apply MeasureTheory.Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun a => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg (realRowDot a u)])
  have hbridge : expectation (EntryLaw.ternary.rowPMF f)
      (fun a => ENNReal.ofReal (Real.exp (-3 * realRowDot a u ^ 2))) =
      ENNReal.ofReal (∫ a, Real.exp (-3 * realRowDot a u ^ 2)
        ∂(sparseRademacherRow f).toMeasure) := by
    change (∑' a, sparseRademacherRow f a *
      ENNReal.ofReal (Real.exp (-3 * realRowDot a u ^ 2))) = _
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hexp
      (Filter.Eventually.of_forall (fun a => (Real.exp_pos _).le)),
      MeasureTheory.lintegral_countable']
    apply tsum_congr
    intro a
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]
  rw [hbridge]
  calc
    _ ≤ ∏ i ∈ S, gaussianCosineMoment 3 (2 / (u i ^ 2)) ^ (u i ^ 2) :=
      sparseScalarReduction 3 u S hS (by norm_num) hu
    _ ≤ ∏ i ∈ S, ENNReal.ofReal (262447 / 500000) ^ (u i ^ 2) := by
      apply Finset.prod_le_prod'
      intro i hi
      apply ENNReal.rpow_le_rpow _ (sq_nonneg _)
      exact cosineMoment_three_le (u i ^ 2)
        (sq_pos_of_ne_zero ((hS i).mp hi)) (hweight i)
    _ = ENNReal.ofReal (262447 / 500000) := by
      simp_rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 262447 / 500000)]
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 262447 / 500000),
          hsum, Real.rpow_one]
      · intro i hi
        positivity
    _ ≤ ENNReal.ofReal (21 / 40) := ENNReal.ofReal_le_ofReal (by norm_num)

end CertifiedProjections.MultiStage
