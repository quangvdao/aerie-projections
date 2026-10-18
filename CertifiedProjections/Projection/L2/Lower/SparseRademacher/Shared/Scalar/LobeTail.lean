/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.LobePeriodization
import CertifiedProjections.Analysis.Gaussian.IntegerGaussianTail
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quantified large-exponent scalar lobe tail

This module is the first consumer of the full L6 integer sum.  It keeps the
zero image separate from the nonzero image tail and only then applies the
quadratic-to-geometric estimate `k^2 ≥ 1 + 3(k-1)` encoded by the shared
periodization producer.  No finite certificate data is imported here.
-/

open scoped BigOperators

namespace CertifiedProjections

/-- The real two-sided discrete Gaussian series is summable. -/
theorem summable_real_integer_exp_neg_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith)
    intro n
    cases n with
    | zero => simp
    | succ n =>
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith [sq_nonneg (n : ℝ)]
  · apply Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith)
    intro n
    cases n with
    | zero => simp
    | succ n =>
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith [sq_nonneg (n : ℝ)]

/-- The shared ENNReal geometric estimate, converted back to a real series. -/
theorem scalarLobe_real_integer_exp_geometricTail {c : ℝ} (hc : 0 < c) :
    ∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2) ≤
      1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) := by
  have hρ : Real.exp (-c) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc)
  have hρcube : (Real.exp (-c)) ^ 3 < 1 := by
    simpa using (pow_lt_pow_left₀ hρ (Real.exp_pos (-c)).le
      (by norm_num : (3 : ℕ) ≠ 0))
  have hden : 0 < 1 - (Real.exp (-c)) ^ 3 := sub_pos.mpr hρcube
  have hbound :
      0 ≤ (1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) : ℝ) := by
    have htail : 0 ≤ 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) :=
      div_nonneg (by positivity) hden.le
    linarith
  have h := integerGaussian_exp_geometricTail c hc
  have hreal := ENNReal.toReal_le_of_le_ofReal
    hbound h
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at hreal
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ENNReal.toReal_ofReal (by positivity)] using hreal

/-- The nonzero real image series is bounded independently of its zero image. -/
theorem scalarLobe_real_integer_exp_nonzero_geometricTail {c : ℝ} (hc : 0 < c) :
    ∑' k : ℤ, (if k = 0 then (0 : ℝ) else
      Real.exp (-c * (k : ℝ) ^ 2)) ≤
      2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) := by
  have hρ : Real.exp (-c) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc)
  have hρcube : (Real.exp (-c)) ^ 3 < 1 := by
    simpa using (pow_lt_pow_left₀ hρ (Real.exp_pos (-c)).le
      (by norm_num : (3 : ℕ) ≠ 0))
  have hden : 0 < 1 - (Real.exp (-c)) ^ 3 := sub_pos.mpr hρcube
  have hbound :
      0 ≤ (2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) : ℝ) :=
    div_nonneg (by positivity) hden.le
  have h := integerGaussian_exp_nonzero_geometricTail c hc
  have hreal := ENNReal.toReal_le_of_le_ofReal
    hbound h
  rw [ENNReal.tsum_toReal_eq (fun k => by
    split <;> simp)] at hreal
  have heq :
      (∑' k : ℤ, (if k = 0 then (0 : ℝ) else
        Real.exp (-c * (k : ℝ) ^ 2))) =
        ∑' k : ℤ, ENNReal.toReal (if k = 0 then 0 else
          ENNReal.ofReal (Real.exp (-c * (k : ℝ) ^ 2))) := by
    apply tsum_congr
    intro k
    split
    · simp
    · rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  calc
    (∑' k : ℤ, (if k = 0 then (0 : ℝ) else
        Real.exp (-c * (k : ℝ) ^ 2))) =
        ∑' k : ℤ, ENNReal.toReal (if k = 0 then 0 else
          ENNReal.ofReal (Real.exp (-c * (k : ℝ) ^ 2))) := heq
    _ ≤ 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) := hreal

/-- The zero/nonzero split reconstructs the complete real Gaussian series. -/
theorem scalarLobe_real_integer_exp_zero_add_nonzero {c : ℝ} (hc : 0 < c) :
    ∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2) =
      1 + ∑' k : ℤ, (if k = 0 then (0 : ℝ) else
        Real.exp (-c * (k : ℝ) ^ 2)) := by
  rw [(summable_real_integer_exp_neg_sq hc).tsum_eq_add_tsum_ite 0]
  norm_num

/-- At `s=13/4`, every exponent `p≥8` is controlled by the geometric lobe
series at the endpoint exponent `c = 16*pi^2/17`. -/
theorem sparseScalarF_lobe_periodization_p_ge_eight {p : ℝ} (hp : 8 ≤ p) :
    sparseScalarF (13 / 4) p ≤
      (2 / Real.sqrt 17) *
        (1 + 2 * Real.exp (-(16 * Real.pi ^ 2 / 17)) /
          (1 - (Real.exp (-(16 * Real.pi ^ 2 / 17))) ^ 3)) := by
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  let c : ℝ := 16 * Real.pi ^ 2 / 17
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hL6 := sparseScalarF_lobe_periodization
    (s := (13 / 4 : ℝ)) (p := p) (by norm_num) hp_pos
  have hterm (k : ℤ) :
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
        (2 * (1 + (13 / 4 : ℝ)))) ≤
        Real.exp (-c * (k : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hcoeff :
        16 * Real.pi ^ 2 / 17 ≤ 2 * p * Real.pi ^ 2 / 17 := by
      nlinarith [sq_pos_of_pos Real.pi_pos]
    have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (k : ℝ))
    calc
      -(p * ((k : ℝ) * Real.pi) ^ 2) /
          (2 * (1 + (13 / 4 : ℝ))) =
          -(2 * p * Real.pi ^ 2 / 17 * (k : ℝ) ^ 2) := by
            norm_num
            ring
      _ ≤ -(16 * Real.pi ^ 2 / 17 * (k : ℝ) ^ 2) := by
        nlinarith [hmul]
      _ = -c * (k : ℝ) ^ 2 := by
        dsimp [c]
        ring
  have hsource :
      Summable (fun k : ℤ =>
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
          (2 * (1 + (13 / 4 : ℝ))))) :=
    (summable_real_integer_exp_neg_sq hc).of_nonneg_of_le
      (fun k => by positivity) hterm
  have hc_source : 0 < 2 * p * Real.pi ^ 2 / 17 := by
    positivity
  have hsource_eq (k : ℤ) :
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
        (2 * (1 + (13 / 4 : ℝ)))) =
        Real.exp (-(2 * p * Real.pi ^ 2 / 17 * (k : ℝ) ^ 2)) := by
    congr 1
    norm_num
    ring
  have hsource_eq_nz (k : ℤ) :
      (if k = 0 then (0 : ℝ) else
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
          (2 * (1 + (13 / 4 : ℝ))))) =
        (if k = 0 then (0 : ℝ) else
          Real.exp (-(2 * p * Real.pi ^ 2 / 17 * (k : ℝ) ^ 2))) := by
    split
    · rfl
    · rw [hsource_eq]
  have hsource_split_generic :=
    scalarLobe_real_integer_exp_zero_add_nonzero hc_source
  have hsource_split :
      (∑' k : ℤ,
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
          (2 * (1 + (13 / 4 : ℝ))))) =
        1 + ∑' k : ℤ, (if k = 0 then (0 : ℝ) else
          Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
            (2 * (1 + (13 / 4 : ℝ))))) := by
    calc
      (∑' k : ℤ,
          Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
            (2 * (1 + (13 / 4 : ℝ))))) =
          ∑' k : ℤ, Real.exp
            (-(2 * p * Real.pi ^ 2 / 17 * (k : ℝ) ^ 2)) := by
        apply tsum_congr
        intro k
        exact hsource_eq k
      _ = 1 + ∑' k : ℤ, (if k = 0 then (0 : ℝ) else
            Real.exp (-(2 * p * Real.pi ^ 2 / 17 * (k : ℝ) ^ 2))) :=
        (by simpa only [neg_mul] using hsource_split_generic)
      _ = 1 + ∑' k : ℤ, (if k = 0 then (0 : ℝ) else
            Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
              (2 * (1 + (13 / 4 : ℝ))))) := by
        congr 1
        apply tsum_congr
        intro k
        exact (hsource_eq_nz k).symm
  have hsource_nonzero :
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
          (2 * (1 + (13 / 4 : ℝ))))) :=
    hsource.of_nonneg_of_le
      (fun k => by split <;> positivity)
      (fun k => by
        split
        · positivity
        · exact le_rfl)
  have htarget_nonzero :
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
        Real.exp (-c * (k : ℝ) ^ 2)) :=
    (summable_real_integer_exp_neg_sq hc).of_nonneg_of_le
      (fun k => by split <;> positivity)
      (fun k => by
        split
        · positivity
        · exact le_rfl)
  have hnonzero_sum :
      (∑' k : ℤ, (if k = 0 then (0 : ℝ) else
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
          (2 * (1 + (13 / 4 : ℝ)))))) ≤
      ∑' k : ℤ, (if k = 0 then (0 : ℝ) else
        Real.exp (-c * (k : ℝ) ^ 2)) := by
    apply hsource_nonzero.tsum_le_tsum
    · intro k
      split
      · simp
      · exact hterm k
    · exact htarget_nonzero
  have htail := scalarLobe_real_integer_exp_nonzero_geometricTail hc
  have hsum_bound :
      (∑' k : ℤ,
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
          (2 * (1 + (13 / 4 : ℝ))))) ≤
        1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) := by
    calc
      (∑' k : ℤ,
          Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
            (2 * (1 + (13 / 4 : ℝ))))) =
          1 + ∑' k : ℤ, (if k = 0 then (0 : ℝ) else
            Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
              (2 * (1 + (13 / 4 : ℝ))))) := hsource_split
      _ ≤ 1 + ∑' k : ℤ, (if k = 0 then (0 : ℝ) else
            Real.exp (-c * (k : ℝ) ^ 2)) :=
        add_le_add_right hnonzero_sum 1
      _ ≤ 1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) :=
        add_le_add_right htail 1
  calc
    sparseScalarF (13 / 4) p ≤
        1 / Real.sqrt (1 + (13 / 4 : ℝ)) *
          ∑' k : ℤ,
            Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
              (2 * (1 + (13 / 4 : ℝ)))) := hL6
    _ ≤ 1 / Real.sqrt (1 + (13 / 4 : ℝ)) *
          (1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) := by
      apply mul_le_mul_of_nonneg_left hsum_bound
      positivity
    _ = (2 / Real.sqrt 17) *
          (1 + 2 * Real.exp (-(16 * Real.pi ^ 2 / 17)) /
            (1 - (Real.exp (-(16 * Real.pi ^ 2 / 17))) ^ 3)) := by
      dsimp [c]
      have hsqrt : Real.sqrt (1 + (13 / 4 : ℝ)) = Real.sqrt 17 / 2 := by
        rw [show 1 + (13 / 4 : ℝ) = 17 / 4 by norm_num]
        rw [Real.sqrt_div (by norm_num : 0 ≤ (17 : ℝ))]
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
            Real.sqrt_nonneg (4 : ℝ)]
        rw [hsqrt4]
      have hsqrt17 : 0 < Real.sqrt (17 : ℝ) := Real.sqrt_pos.2 (by norm_num)
      rw [hsqrt]
      have hfactor : 1 / (Real.sqrt 17 / 2) = 2 / Real.sqrt 17 := by
        field_simp [ne_of_gt hsqrt17]
      rw [hfactor]

/-- A coupled lower bound on the exponent and tilt controls the lobe series
without replacing them by independent box endpoints.  This is the form
needed by threshold-relative diffuse profiles, where normalization gives
`p ≥ r * s` and both quantities grow with the selected squared mass. -/
theorem sparseScalarF_lobe_periodization_of_tilt_ratio
    {s p sLower r : ℝ}
    (hsLower : 0 < sLower) (hs : sLower ≤ s)
    (hr : 0 < r) (hp : r * s ≤ p) :
    sparseScalarF s p ≤
      1 / Real.sqrt (1 + sLower) *
        (1 + 2 * Real.exp
            (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) /
          (1 - (Real.exp
            (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))))) ^ 3)) := by
  have hs_pos : 0 < s := hsLower.trans_le hs
  have hp_pos : 0 < p := lt_of_lt_of_le (mul_pos hr hs_pos) hp
  let c : ℝ := r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hratio : r * sLower / (1 + sLower) ≤ p / (1 + s) := by
    have hdenLower : 0 < 1 + sLower := by linarith
    have hden : 0 < 1 + s := by linarith
    apply (div_le_div_iff₀ hdenLower hden).2
    have hs0 : 0 ≤ sLower := hsLower.le
    have hrs := mul_le_mul_of_nonneg_left hs hr.le
    nlinarith
  have hcoefficient : c ≤ p * Real.pi ^ 2 / (2 * (1 + s)) := by
    dsimp [c]
    have hpi : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hratio hpi
    have hhalf := mul_le_mul_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)) =
          (r * sLower / (1 + sLower) * Real.pi ^ 2) * (1 / 2) := by
        field_simp [show 1 + sLower ≠ 0 by linarith]
      _ ≤ (p / (1 + s) * Real.pi ^ 2) * (1 / 2) := hhalf
      _ = p * Real.pi ^ 2 / (2 * (1 + s)) := by
        field_simp [show 1 + s ≠ 0 by linarith]
  have hterm (k : ℤ) :
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) ≤
        Real.exp (-c * (k : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hcoefficient
      (sq_nonneg (k : ℝ))
    calc
      -(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)) =
          -(p * Real.pi ^ 2 / (2 * (1 + s)) * (k : ℝ) ^ 2) := by ring
      _ ≤ -(c * (k : ℝ) ^ 2) := by linarith
      _ = -c * (k : ℝ) ^ 2 := by ring
  have hsource : Summable (fun k : ℤ =>
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) :=
    (summable_real_integer_exp_neg_sq hc).of_nonneg_of_le
      (fun _ => by positivity) hterm
  have hsum :
      (∑' k : ℤ,
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) ≤
        1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) := by
    exact (hsource.tsum_le_tsum hterm
      (summable_real_integer_exp_neg_sq hc)).trans
        (scalarLobe_real_integer_exp_geometricTail hc)
  have hL6 := sparseScalarF_lobe_periodization hs_pos hp_pos
  have hsqrt :
      1 / Real.sqrt (1 + s) ≤ 1 / Real.sqrt (1 + sLower) := by
    have hsqrt_pos : 0 < Real.sqrt (1 + sLower) := by positivity
    exact one_div_le_one_div_of_le hsqrt_pos
      (Real.sqrt_le_sqrt (by linarith))
  have hfactor_nonneg :
      0 ≤ 1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) := by
    have hexp_lt : Real.exp (-c) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    have hpow : (Real.exp (-c)) ^ 3 < 1 :=
      pow_lt_one₀ (Real.exp_nonneg _) hexp_lt (by norm_num)
    positivity
  calc
    sparseScalarF s p ≤
        1 / Real.sqrt (1 + s) *
          ∑' k : ℤ,
            Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
              (2 * (1 + s))) := hL6
    _ ≤ 1 / Real.sqrt (1 + s) *
        (1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 1 / Real.sqrt (1 + sLower) *
        (1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) :=
      mul_le_mul_of_nonneg_right hsqrt hfactor_nonneg
    _ = 1 / Real.sqrt (1 + sLower) *
        (1 + 2 * Real.exp
            (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower)))) /
          (1 - (Real.exp
            (-(r * sLower * Real.pi ^ 2 / (2 * (1 + sLower))))) ^ 3)) := by
      rfl

end CertifiedProjections
