/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian cosine transforms

Scalar analytic consumers use these Gaussian characteristic-function
identities without depending on the finite sparse-entry or row model.  The
finite-PMF Fourier bridge imports this module and adds the row-specific
factors separately.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

/-- The cosine is integrable against the standard Gaussian for every frequency. -/
theorem gaussian_cos_integrable (t : ℝ) :
    Integrable (fun G : ℝ => Real.cos (t * G)) (gaussianReal 0 1) := by
  refine Integrable.of_bound
    (by fun_prop) 1 ?_
  filter_upwards [] with G
  simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * G)

theorem gaussian_cosine_charFun (t : ℝ) :
    ∫ x : ℝ, Real.cos (t * x) ∂(gaussianReal 0 1) =
      Real.exp (-t ^ 2 / 2) := by
  have h_int :
      Integrable (fun x : ℝ => Complex.exp ((t * x) * Complex.I))
        (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · fun_prop
    · filter_upwards with x
      simpa only [Complex.ofReal_mul] using
        (Complex.norm_exp_ofReal_mul_I (t * x)).le
  have h_re := integral_re h_int
  calc
    ∫ x : ℝ, Real.cos (t * x) ∂(gaussianReal 0 1) =
        ∫ x : ℝ, (Complex.exp ((t * x) * Complex.I)).re
          ∂(gaussianReal 0 1) := by
      congr 1
      funext x
      simpa only [Complex.ofReal_mul] using
        (Complex.exp_ofReal_mul_I_re (t * x)).symm
    _ = (MeasureTheory.charFun (gaussianReal 0 1) t).re := by
      rw [MeasureTheory.charFun_apply_real]
      rw [← RCLike.re_eq_complex_re]
      exact h_re
    _ = Real.exp (-t ^ 2 / 2) := by
      rw [ProbabilityTheory.charFun_gaussianReal]
      simp [Complex.exp_re, pow_two]
      ring

/-- A Gaussian cosine integral is the negative Laplace kernel. -/
theorem gaussian_cosine_kernel (s x : ℝ) (hs : 0 ≤ s) :
    Real.exp (-s * x ^ 2) =
      ∫ G : ℝ, Real.cos (Real.sqrt (2 * s) * G * x)
        ∂(gaussianReal 0 1) := by
  have h2s : 0 ≤ 2 * s := by positivity
  have hsqrt : (Real.sqrt (2 * s)) ^ 2 = 2 * s := Real.sq_sqrt h2s
  calc
    Real.exp (-s * x ^ 2) =
        Real.exp (-(Real.sqrt (2 * s) * x) ^ 2 / 2) := by
      congr 1
      rw [mul_pow, hsqrt]
      ring
    _ = ∫ G : ℝ, Real.cos ((Real.sqrt (2 * s) * x) * G)
        ∂(gaussianReal 0 1) :=
      (gaussian_cosine_charFun (Real.sqrt (2 * s) * x)).symm
    _ = ∫ G : ℝ, Real.cos (Real.sqrt (2 * s) * G * x)
        ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      congr 1
      ring

/-- A Gaussian complex-exponential integral is the negative quadratic kernel. -/
theorem gaussian_complex_exponential_kernel (s x : ℝ) (hs : 0 ≤ s) :
    (Real.exp (-s * x ^ 2) : ℂ) =
      ∫ G : ℝ, Complex.exp
        (Complex.I * (Real.sqrt (2 * s) * G * x : ℝ))
        ∂(gaussianReal 0 1) := by
  have h2s : 0 ≤ 2 * s := by positivity
  have hsqrt : (Real.sqrt (2 * s)) ^ 2 = 2 * s := Real.sq_sqrt h2s
  let t : ℝ := Real.sqrt (2 * s) * x
  calc
    (Real.exp (-s * x ^ 2) : ℂ) = Complex.exp (-(t : ℂ) ^ 2 / 2) := by
      rw [Complex.ofReal_exp]
      congr 1
      norm_cast
      dsimp only [t]
      rw [mul_pow, hsqrt]
      ring
    _ = MeasureTheory.charFun (gaussianReal 0 1) t := by
      rw [ProbabilityTheory.charFun_gaussianReal]
      congr 1
      push_cast
      ring
    _ = ∫ G : ℝ, Complex.exp
        (Complex.I * (Real.sqrt (2 * s) * G * x : ℝ))
        ∂(gaussianReal 0 1) := by
      rw [MeasureTheory.charFun_apply_real]
      apply integral_congr_ae
      filter_upwards [] with G
      congr 1
      dsimp only [t]
      simp only [Complex.ofReal_mul]
      ring

end CertifiedProjections
