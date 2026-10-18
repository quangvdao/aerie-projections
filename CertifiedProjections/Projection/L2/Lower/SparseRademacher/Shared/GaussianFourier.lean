/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Distributions.Entry
import CertifiedProjections.Model.Vectors.Real
import CertifiedProjections.Analysis.Gaussian.GaussianCharacteristic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian Fourier bridge for sparse lower tails

This module begins the analytic identity that turns a sparse-row negative-argument MGF into a Gaussian cosine product.  The first lemma is kept
separate from the finite sparse-row calculation: it exposes exactly where
the Gaussian characteristic-function theorem enters the proof.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

/-! ## The finite sparse-entry Fourier factor -/

theorem sparseEntry_cosine (t : ℝ) :
    ∫ z, Real.cos ((z : ℝ) * t) ∂sparseEntryPMF.toMeasure =
      (1 + Real.cos t) / 2 := by
  rw [sparseEntryPMF]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (Bool × Bool)) (f := sparseBit)
    (measurable_of_finite sparseBit)]
  rw [integral_map_of_stronglyMeasurable
    (measurable_of_finite sparseBit)
    (measurable_of_countable
      (fun z : ℤ => Real.cos ((z : ℝ) * t))).stronglyMeasurable]
  rw [finitePMF_integral_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, sparseBit]
  ring

/-- The sparse-entry complex characteristic factor is real and explicit. -/
theorem sparseEntry_char (t : ℝ) :
    ∫ z, Complex.exp ((z : ℝ) * t * Complex.I)
        ∂sparseEntryPMF.toMeasure =
      ((1 + Real.cos t) / 2 : ℂ) := by
  rw [sparseEntryPMF]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (Bool × Bool)) (f := sparseBit)
    (measurable_of_finite sparseBit)]
  rw [integral_map_of_stronglyMeasurable
    (measurable_of_finite sparseBit)
    (measurable_of_countable
      (fun z : ℤ => Complex.exp ((z : ℝ) * t * Complex.I))).stronglyMeasurable]
  rw [finitePMF_integral_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp only [Fintype.univ_bool, PMF.uniformOfFintype_apply, Fintype.card_prod,
    Fintype.card_bool, Nat.reduceMul, Nat.cast_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, Complex.ofReal_intCast, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_ofNat, Finset.mem_singleton,
    sparseBit, Int.cast_neg, Int.cast_zero, Int.cast_one,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, Complex.ofReal_cos, zero_mul,
    one_mul, neg_mul, Complex.exp_zero]
  rw [show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.ofReal_neg, neg_mul, Complex.ofReal_cos,
    Complex.ofReal_sin]
  rw [show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul,
    Complex.ofReal_cos, Complex.ofReal_sin]
  ring_nf

/-- The sparse-row complex characteristic function factors over entries. -/
theorem sparseRow_char (d : ℕ) (u : ℝ) (a : Fin d → ℝ) :
    ∫ row, Complex.exp (u * realRowDot row a * Complex.I)
        ∂(sparseRademacherRow d).toMeasure =
      ∏ i, ((1 + Real.cos (u * a i)) / 2 : ℂ) := by
  rw [sparseRademacherRow_toMeasure]
  calc
    ∫ row, Complex.exp (u * realRowDot row a * Complex.I)
        ∂Measure.pi (fun _ : Fin d => sparseEntryPMF.toMeasure) =
        ∫ row, ∏ i, Complex.exp
          (u * (row i : ℝ) * a i * Complex.I)
          ∂Measure.pi (fun _ : Fin d => sparseEntryPMF.toMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with row
      simp only [realRowDot]
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
      congr 1
      funext i
      ring_nf
    _ = ∏ i, ∫ z, Complex.exp
          (u * (z : ℝ) * a i * Complex.I)
          ∂sparseEntryPMF.toMeasure :=
      integral_fintype_prod_eq_prod
        (μ := fun _ : Fin d => sparseEntryPMF.toMeasure)
        (fun i (z : ℤ) => Complex.exp
          (u * (z : ℝ) * a i * Complex.I))
    _ = ∏ i, ((1 + Real.cos (u * a i)) / 2 : ℂ) := by
      apply Finset.prod_congr rfl
      intro i hi
      calc
        ∫ z, Complex.exp (u * (z : ℝ) * a i * Complex.I)
            ∂sparseEntryPMF.toMeasure =
            ∫ z, Complex.exp ((z : ℝ) * (u * a i) * Complex.I)
              ∂sparseEntryPMF.toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with z
          congr 1
          ring
        _ = ((1 + Real.cos (u * a i)) / 2 : ℂ) := by
          simpa only [Complex.ofReal_mul] using sparseEntry_char (u * a i)

/-- The real sparse-row cosine transform is the real characteristic factor. -/
theorem sparseRow_cosineTransform (d : ℕ) (u : ℝ) (a : Fin d → ℝ) :
    ∫ row, Real.cos (u * realRowDot row a)
        ∂(sparseRademacherRow d).toMeasure =
      ∏ i, (1 + Real.cos (u * a i)) / 2 := by
  have h_int :
      Integrable (fun row : Fin d → ℤ =>
        Complex.exp (u * realRowDot row a * Complex.I))
        (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (measurable_of_countable
        (fun row : Fin d → ℤ =>
          Complex.exp (u * realRowDot row a * Complex.I))).aestronglyMeasurable
    · filter_upwards with row
      simpa only [Complex.ofReal_mul] using
        (Complex.norm_exp_ofReal_mul_I (u * realRowDot row a)).le
  have h_re := integral_re h_int
  calc
    ∫ row, Real.cos (u * realRowDot row a)
        ∂(sparseRademacherRow d).toMeasure =
        ∫ row, (Complex.exp (u * realRowDot row a * Complex.I)).re
          ∂(sparseRademacherRow d).toMeasure := by
      congr 1
      funext row
      simpa only [Complex.ofReal_mul] using
        (Complex.exp_ofReal_mul_I_re
          (u * realRowDot row a)).symm
    _ = (∫ row, Complex.exp (u * realRowDot row a * Complex.I)
          ∂(sparseRademacherRow d).toMeasure).re := by
      rw [← RCLike.re_eq_complex_re]
      exact h_re
    _ = (∏ i, ((1 + Real.cos (u * a i)) / 2 : ℂ)).re := by
      rw [sparseRow_char]
    _ = ∏ i, (1 + Real.cos (u * a i)) / 2 := by
      norm_cast

/-- The sparse-row cosine transform factors over the independent entries. -/
theorem sparseRow_cosineProduct (d : ℕ) (u : ℝ) (a : Fin d → ℝ) :
    ∫ row, ∏ i, Real.cos (u * (row i : ℝ) * a i)
        ∂(sparseRademacherRow d).toMeasure =
      ∏ i, (1 + Real.cos (u * a i)) / 2 := by
  rw [sparseRademacherRow_toMeasure]
  calc
    ∫ row, ∏ i, Real.cos (u * (row i : ℝ) * a i)
        ∂Measure.pi (fun _ : Fin d => sparseEntryPMF.toMeasure) =
        ∏ i, ∫ z, Real.cos (u * (z : ℝ) * a i)
          ∂sparseEntryPMF.toMeasure := by
      simpa only [mul_assoc] using
        (integral_fintype_prod_eq_prod
          (μ := fun _ : Fin d => sparseEntryPMF.toMeasure)
          (fun i (z : ℤ) => Real.cos (u * (z : ℝ) * a i)))
    _ = ∏ i, (1 + Real.cos (u * a i)) / 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      calc
        ∫ z, Real.cos (u * (z : ℝ) * a i) ∂sparseEntryPMF.toMeasure =
            ∫ z, Real.cos ((z : ℝ) * (u * a i))
              ∂sparseEntryPMF.toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with z
          congr 1
          ring
        _ = (1 + Real.cos (u * a i)) / 2 := sparseEntry_cosine (u * a i)

/-! ## The row-level Gaussian Fourier identity -/

/--
The sparse-row negative-argument MGF is a Gaussian cosine product.
The proof uses the product measure of the finite row PMF and an explicit
Bochner Fubini step; no finite-support transport or external certificate is
hidden in this identity.
-/
theorem sparseRow_negativeMGF_fourier
    (d : ℕ) (s : ℝ) (a : Fin d → ℝ) (hs : 0 ≤ s) :
    ∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow d).toMeasure =
      ∫ G : ℝ, ∏ i, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2
        ∂(gaussianReal 0 1) := by
  let μrow : Measure (Fin d → ℤ) := (sparseRademacherRow d).toMeasure
  let μgauss : Measure ℝ := gaussianReal 0 1
  let f : (Fin d → ℤ) → ℝ → ℝ := fun row G =>
    Real.cos (Real.sqrt (2 * s) * G * realRowDot row a)
  have hrow : Measurable (fun row : Fin d → ℤ => realRowDot row a) :=
    measurable_of_countable _
  have harg : Measurable (fun p : (Fin d → ℤ) × ℝ =>
      Real.sqrt (2 * s) * p.2 * realRowDot p.1 a) := by
    exact (measurable_const.mul measurable_snd).mul
      (hrow.comp measurable_fst)
  have hf_meas : Measurable (Function.uncurry f) := by
    exact Real.continuous_cos.measurable.comp harg
  have hf_int : Integrable (Function.uncurry f) (μrow.prod μgauss) := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 ?_
    filter_upwards [] with p
    change |Real.cos (Real.sqrt (2 * s) * p.2 * realRowDot p.1 a)| ≤ 1
    exact Real.abs_cos_le_one _
  calc
    ∫ row, Real.exp (-s * (realRowDot row a) ^ 2) ∂μrow =
        ∫ row, ∫ G : ℝ, f row G ∂μgauss ∂μrow := by
      apply integral_congr_ae
      filter_upwards [] with row
      simpa only [f] using gaussian_cosine_kernel s (realRowDot row a) hs
    _ = ∫ G : ℝ, ∫ row, f row G ∂μrow ∂μgauss :=
      integral_integral_swap hf_int
    _ = ∫ G : ℝ, ∏ i, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2
          ∂μgauss := by
      apply integral_congr_ae
      filter_upwards [] with G
      simpa only [f] using sparseRow_cosineTransform d
        (Real.sqrt (2 * s) * G) a

/-! ## A bounded row-integral corollary -/

theorem sparseRow_negativeMGF_fourier_nonneg
    (d : ℕ) (s : ℝ) (a : Fin d → ℝ) (_hs : 0 ≤ s) :
    0 ≤ ∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow d).toMeasure := by
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall
    (fun row => Real.exp_nonneg _))

end CertifiedProjections
