/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedProjections.Certificates.Families.L2Lower.Shared.Dense.Soundness.DenseScalarP3TightCertificate
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Regimes.Dense.ScalarEndpoints
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.LogConvexity
import CertifiedProjections.Arithmetic.Interval.Reflection
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Dense scalar interpolation envelope

This module is the semantic/certificate boundary for the compact dense
`[3,8]` profile.  It consumes the paper-facing L5 producer, but replaces its
square-root correction by the elementary harmonic-mean envelope.  That keeps
the local numerical obligations polynomial in the interpolation parameter;
the finite certificate never treats sampled endpoints as a universal proof.
-/

open scoped BigOperators

namespace CertifiedProjections
namespace DenseScalar

private theorem dense_exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck
      (Exp.negUpper p3CertificatePrecision x p3CertificateSquarings) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  have hcontains := Exp.negUpper_contains
    (p := p3CertificatePrecision) (k := p3CertificateSquarings)
    (x := x) hx
  exact Interval.lt_of_contains_of_upperLTCheck hcontains hcheck

/-! The following four bounds are deliberately tighter than the final target.
They are checked by the same transparent exponential enclosure as the p=3
certificate, but use only positive endpoint coefficients. -/

/- The endpoint check is a transparent kernel reduction over exact dyadics. -/
theorem sparseScalarF_13_div_4_four_lt_474_over_1000 :
    sparseScalarF (13 / 4) 4 < (474 / 1000 : ℝ) := by
  have h13 := dense_exp_neg_lt (x := (13 / 8 : ℚ)) (u := (197 / 1000 : ℚ))
    (by norm_num) (by decide +kernel)
  have h26 := dense_exp_neg_lt (x := (13 / 2 : ℚ)) (u := (2 / 1000 : ℚ))
    (by norm_num) (by decide +kernel)
  rw [sparseScalarF_13_div_4_four_exact]
  nlinarith

/- The endpoint check is a transparent kernel reduction over exact dyadics. -/
theorem sparseScalarF_13_div_4_six_lt_474_over_1000 :
    sparseScalarF (13 / 4) 6 < (474 / 1000 : ℝ) := by
  have h13 := dense_exp_neg_lt (x := (13 / 12 : ℚ)) (u := (1693 / 5000 : ℚ))
    (by norm_num) (by decide +kernel)
  have h26 := dense_exp_neg_lt (x := (13 / 3 : ℚ)) (u := (14 / 1000 : ℚ))
    (by norm_num) (by decide +kernel)
  have h39 := dense_exp_neg_lt (x := (39 / 4 : ℚ)) (u := (1 / 1000 : ℚ))
    (by norm_num) (by decide +kernel)
  rw [sparseScalarF_13_div_4_six_exact]
  nlinarith

/- The endpoint check is a transparent kernel reduction over exact dyadics. -/
theorem sparseScalarF_13_div_4_eight_lt_477_over_1000 :
    sparseScalarF (13 / 4) 8 < (477 / 1000 : ℝ) := by
  have h13 := dense_exp_neg_lt (x := (13 / 16 : ℚ)) (u := (445 / 1000 : ℚ))
    (by norm_num) (by decide +kernel)
  have h26 := dense_exp_neg_lt (x := (13 / 4 : ℚ)) (u := (39 / 1000 : ℚ))
    (by norm_num) (by decide +kernel)
  have h39 := dense_exp_neg_lt (x := (117 / 16 : ℚ)) (u := (1 / 1000 : ℚ))
    (by norm_num) (by decide +kernel)
  have h52 := dense_exp_neg_lt (x := (13 : ℚ)) (u := (1 / 1000 : ℚ))
    (by norm_num) (by decide +kernel)
  rw [sparseScalarF_13_div_4_eight_exact]
  nlinarith

/-! An L5 consumer with no logarithms.  The harmonic-mean form is the exact
bridge used by the finite polynomial cells below. -/

theorem sparseScalarF_mul_sqrt_harmonic_le {s a b p θ A B : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hp0 : 0 < p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : p = (1 - θ) * a + θ * b)
    (hFa : sparseScalarF s a ≤ A) (hFb : sparseScalarF s b ≤ B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    sparseScalarF s p ≤
      ((1 - θ) * A + θ * B) *
        Real.sqrt (p * ((1 - θ) / a + θ / b)) := by
  have hmul := sparseScalarF_mul_rpow_sqrt_le
    hs ha hb hab hp0 hθ0 hθ1 hp
  have hFa0 : 0 ≤ sparseScalarF s a :=
    (sparseScalarF_pos hs ha).le
  have hFb0 : 0 ≤ sparseScalarF s b :=
    (sparseScalarF_pos hs hb).le
  have hgeom := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr hθ1) hθ0 hFa0 hFb0 (by ring : (1 - θ) + θ = 1)
  have hgeomAB :
      sparseScalarF s a ^ (1 - θ) * sparseScalarF s b ^ θ ≤
        (1 - θ) * A + θ * B := by
    calc
      sparseScalarF s a ^ (1 - θ) * sparseScalarF s b ^ θ ≤
          (1 - θ) * sparseScalarF s a + θ * sparseScalarF s b := hgeom
      _ ≤ (1 - θ) * A + θ * B := by
        gcongr
  have hlinear : 0 ≤ (1 - θ) * A + θ * B := by positivity
  have hden_inv :
      (a ^ (1 - θ) * b ^ θ)⁻¹ ≤ (1 - θ) / a + θ / b := by
    have hgm := Real.geom_mean_le_arith_mean2_weighted
      (sub_nonneg.mpr hθ1) hθ0 (by positivity : 0 ≤ (1 / a : ℝ))
      (by positivity : 0 ≤ (1 / b : ℝ)) (by ring : (1 - θ) + θ = 1)
    have hrewrite :
        (1 / a : ℝ) ^ (1 - θ) * (1 / b : ℝ) ^ θ =
          (a ^ (1 - θ) * b ^ θ)⁻¹ := by
      rw [one_div, one_div, Real.inv_rpow ha.le, Real.inv_rpow hb.le]
      rw [← mul_inv]
    rw [hrewrite] at hgm
    simpa [div_eq_mul_inv] using hgm
  have hratio :
      p / (a ^ (1 - θ) * b ^ θ) ≤
        p * ((1 - θ) / a + θ / b) := by
    have := mul_le_mul_of_nonneg_left hden_inv hp0.le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hsqrt := Real.sqrt_le_sqrt hratio
  calc
    sparseScalarF s p ≤
        sparseScalarF s a ^ (1 - θ) * sparseScalarF s b ^ θ *
          Real.sqrt (p / (a ^ (1 - θ) * b ^ θ)) := hmul
    _ ≤ ((1 - θ) * A + θ * B) *
          Real.sqrt (p / (a ^ (1 - θ) * b ^ θ)) := by
      exact mul_le_mul_of_nonneg_right hgeomAB (Real.sqrt_nonneg _)
    _ ≤ ((1 - θ) * A + θ * B) *
          Real.sqrt (p * ((1 - θ) / a + θ / b)) := by
      exact mul_le_mul_of_nonneg_left hsqrt hlinear

end DenseScalar
end CertifiedProjections
