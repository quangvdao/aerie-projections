/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.Moment
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Positive scalar moments and Gaussian change of variables

This is the first L5/L6 slice.  It establishes strict positivity before any
future logarithm is introduced.  The real `F_s` moment is positive under the
Gaussian law, and the unnormalised `I_s` lobe integral is positive under
Lebesgue measure.  The later interpolation and lobe partition theorems use
these producers rather than relying on totalized `Real.log` behavior.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

/-- The unnormalised scalar lobe integrand defining `I_s(p)`. -/
noncomputable def scalarLobeIntegrand (s p y : ℝ) : ℝ :=
  Real.rpow
    (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|) p

/-- The paper's positive scalar lobe integral `I_s(p)`. -/
noncomputable def scalarLobeIntegral (s p : ℝ) : ℝ :=
  ∫ y : ℝ, scalarLobeIntegrand s p y

/-- Pointwise scaling identity for the paper substitution
`y = sqrt (s / p) * G`. -/
theorem scalarLobeIntegrand_scale_eq {s p G : ℝ}
    (hs : 0 < s) (hp : 0 < p) :
    scalarLobeIntegrand s p (Real.sqrt (s / p) * G) =
      Real.exp (-G ^ 2 / 2) * sparseScalarFIntegrand s p G := by
  have hsp : 0 ≤ s / p := (div_pos hs hp).le
  have hs0 : s ≠ 0 := hs.ne'
  have hp0 : p ≠ 0 := hp.ne'
  unfold scalarLobeIntegrand sparseScalarFIntegrand
  change
    (Real.exp (-(Real.sqrt (s / p) * G) ^ 2 / (2 * s)) *
        |Real.cos (Real.sqrt (s / p) * G)|) ^ p =
      Real.exp (-G ^ 2 / 2) *
        (|Real.cos (Real.sqrt (s / p) * G)|).rpow p
  rw [Real.mul_rpow (Real.exp_pos _).le (abs_nonneg _)]
  rw [← Real.exp_mul]
  congr 1
  have hsqrt : (Real.sqrt (s / p)) ^ 2 = s / p := Real.sq_sqrt hsp
  rw [mul_pow, hsqrt]
  field_simp

private lemma sparseScalarF_eq_density_integral {s p : ℝ} :
    sparseScalarF s p =
      ∫ G : ℝ, gaussianPDFReal 0 1 G * sparseScalarFIntegrand s p G := by
  unfold sparseScalarF
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]

private lemma gaussian_density_mul_scalar_integrand_eq {s p G : ℝ}
    (hs : 0 < s) (hp : 0 < p) :
    gaussianPDFReal 0 1 G * sparseScalarFIntegrand s p G =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        scalarLobeIntegrand s p (Real.sqrt (s / p) * G) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, sub_zero, mul_one]
  rw [scalarLobeIntegrand_scale_eq hs hp]
  ring

private lemma gaussian_change_factor {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (s / p))⁻¹ =
      Real.sqrt (p / (2 * Real.pi * s)) := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hsp : 0 ≤ s / p := (div_pos hs hp).le
  have hden : 0 ≤ 2 * Real.pi * s := by positivity
  have hleft : 0 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (s / p))⁻¹ := by
    positivity
  have hright : 0 ≤ Real.sqrt (p / (2 * Real.pi * s)) := Real.sqrt_nonneg _
  have hleft_sq :
      ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (s / p))⁻¹) ^ 2 =
        p / (2 * Real.pi * s) := by
    rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt hpi, Real.sq_sqrt hsp]
    field_simp
  have hright_sq :
      (Real.sqrt (p / (2 * Real.pi * s))) ^ 2 =
        p / (2 * Real.pi * s) := by
    exact Real.sq_sqrt (by positivity)
  nlinarith

/-- Exact Gaussian change of variables from `F_s(p)` to the lobe integral
`I_s(p)`, with the paper's normalization. -/
theorem sparseScalarF_eq_sqrt_mul_scalarLobeIntegral {s p : ℝ}
    (hs : 0 < s) (hp : 0 < p) :
    sparseScalarF s p =
      Real.sqrt (p / (2 * Real.pi * s)) * scalarLobeIntegral s p := by
  rw [sparseScalarF_eq_density_integral]
  calc
    (∫ G : ℝ,
        gaussianPDFReal 0 1 G * sparseScalarFIntegrand s p G) =
        ∫ G : ℝ,
          (Real.sqrt (2 * Real.pi))⁻¹ *
            scalarLobeIntegrand s p (Real.sqrt (s / p) * G) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact gaussian_density_mul_scalar_integrand_eq hs hp
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          (∫ G : ℝ,
            scalarLobeIntegrand s p (Real.sqrt (s / p) * G)) := by
      rw [integral_const_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          ((Real.sqrt (s / p))⁻¹ * scalarLobeIntegral s p) := by
      rw [Measure.integral_comp_mul_left]
      simp only [smul_eq_mul]
      rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 (div_pos hs hp)))]
      rfl
    _ = Real.sqrt (p / (2 * Real.pi * s)) * scalarLobeIntegral s p := by
      rw [scalarLobeIntegral, ← mul_assoc, gaussian_change_factor hs hp]

private lemma sparseScalarF_continuous {s p : ℝ} (hp : 0 < p) :
    Continuous (fun G : ℝ => sparseScalarFIntegrand s p G) := by
  have hbase : Continuous (fun G : ℝ =>
      |Real.cos (Real.sqrt (s / p) * G)|) := by
    fun_prop
  exact hbase.rpow_const (fun _ => Or.inr hp.le)

private lemma scalarLobeIntegrand_continuous {s p : ℝ}
    (_hs : 0 < s) (hp : 0 < p) :
    Continuous (fun y : ℝ => scalarLobeIntegrand s p y) := by
  have hbase : Continuous (fun y : ℝ =>
      Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|) := by
    fun_prop
  exact hbase.rpow_const (fun _ => Or.inr hp.le)

private lemma scalarLobeIntegrand_nonneg {s p y : ℝ} :
    0 ≤ scalarLobeIntegrand s p y := by
  exact Real.rpow_nonneg
    (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) _

private lemma scalarLobeIntegrand_le_gaussian {s p y : ℝ}
    (_hs : 0 < s) (hp : 0 < p) :
    ‖scalarLobeIntegrand s p y‖ ≤
      Real.exp (-(p / (2 * s)) * y ^ 2) := by
  have hbase :
      Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y| ≤
        Real.exp (-y ^ 2 / (2 * s)) := by
    calc
      Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y| ≤
          Real.exp (-y ^ 2 / (2 * s)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one y)
          (Real.exp_pos _).le
      _ = Real.exp (-y ^ 2 / (2 * s)) := by ring
  have hpow :
      scalarLobeIntegrand s p y ≤
        Real.rpow (Real.exp (-y ^ 2 / (2 * s))) p := by
    exact Real.rpow_le_rpow
      (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) hbase hp.le
  have hpow_eq :
      Real.rpow (Real.exp (-y ^ 2 / (2 * s))) p =
        Real.exp (-(p / (2 * s)) * y ^ 2) := by
    change (Real.exp (-y ^ 2 / (2 * s)) ^ p : ℝ) = _
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg scalarLobeIntegrand_nonneg]
  exact hpow.trans_eq hpow_eq

/-- Pointwise Gaussian domination used by the `I_s(p)` integrability boundary.

The coefficient `p / (2*s)` is exported because it is part of the reusable
analytic interface, not merely an implementation detail of the integrability
proof.  In particular, later change-of-variables and lobe estimates must not
silently replace it by `1 / (2*s)` or `p / 2`.
-/
theorem scalarLobeIntegrand_norm_le_gaussian {s p y : ℝ}
    (hs : 0 < s) (hp : 0 < p) :
    ‖scalarLobeIntegrand s p y‖ ≤
      Real.exp (-(p / (2 * s)) * y ^ 2) := by
  exact scalarLobeIntegrand_le_gaussian hs hp

/-- The `I_s(p)` integrand is integrable for `s>0,p>0`. -/
theorem scalarLobeIntegrand_integrable {s p : ℝ}
    (hs : 0 < s) (hp : 0 < p) :
    Integrable (fun y : ℝ => scalarLobeIntegrand s p y) := by
  refine (integrable_exp_neg_mul_sq (b := p / (2 * s)) (by positivity)).mono'
    (scalarLobeIntegrand_continuous hs hp).aestronglyMeasurable ?_
  filter_upwards [] with y
  exact scalarLobeIntegrand_norm_le_gaussian hs hp

/-- The Gaussian scalar moment is strictly positive on the L5/L6 domain. -/
theorem sparseScalarF_pos {s p : ℝ} (_hs : 0 < s) (hp : 0 < p) :
    0 < sparseScalarF s p := by
  let : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num)).isOpenPosMeasure
  unfold sparseScalarF
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · exact sparseScalarF_continuous hp
  · exact sparseScalarF_integrable hp
  · intro G
    exact Real.rpow_nonneg (abs_nonneg _) _
  · simp [sparseScalarFIntegrand]

/-- The lobe integral is strictly positive before taking its logarithm. -/
theorem scalarLobeIntegral_pos {s p : ℝ}
    (hs : 0 < s) (hp : 0 < p) :
    0 < scalarLobeIntegral s p := by
  unfold scalarLobeIntegral
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · exact scalarLobeIntegrand_continuous hs hp
  · exact scalarLobeIntegrand_integrable hs hp
  · intro y
    exact scalarLobeIntegrand_nonneg
  · simp [scalarLobeIntegrand]

end CertifiedProjections
