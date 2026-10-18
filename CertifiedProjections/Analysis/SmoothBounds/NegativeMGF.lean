/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Distributions.Entry
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Basic

/-!
# Finite-PMF negative-argument MGF assembly

This module keeps the strict lower event in
the probability statement, proves the finite product integral through the
existing `PMF.toMeasure` bridge, and only then exposes the row-product bound.
No certificate data or external artifact is used here.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

/-! ## Product-PMF bridge -/

/--
The sparse matrix PMF integrates a product of row functions as the product of
the corresponding sparse-row integrals.

The equality is deliberately stated at the `PMF.toMeasure` boundary. This is
the reusable tensorization fact consumed by the strict lower-tail theorem.
-/
theorem sparseRademacherMatrix_integral_prod
    (m d : ℕ) (f : Fin m → (Fin d → ℤ) → ℝ) :
    ∫ J, ∏ j, f j (J j) ∂(sparseRademacherMatrix m d).toMeasure =
      ∏ j, ∫ row, f j row ∂(sparseRademacherRow d).toMeasure := by
  rw [sparseRademacherMatrix_toMeasure]
  exact MeasureTheory.integral_fintype_prod_eq_prod f

/-! ## Strict exponential Markov -/

/--
Strict lower events admit the negative-MGF Markov bound. The proof first
embeds `< c` into the closed event `≤ c`; this makes the strict event
convention explicit without pretending that the final numerical inequality
is strict.
-/
theorem strictExponentialMarkov
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : Ω → ℝ) (s c : ℝ) (hs : 0 < s)
    (h_integrable : Integrable (fun ω => Real.exp (-s * X ω)) μ) :
    μ.real {ω | X ω < c} ≤
      Real.exp (s * c) * ∫ ω, Real.exp (-s * X ω) ∂μ := by
  have h_closed :=
    measure_le_le_exp_mul_mgf (X := X) (μ := μ) (t := -s) c
      (le_of_lt (neg_lt_zero.mpr hs)) h_integrable
  calc
    μ.real {ω | X ω < c} ≤ μ.real {ω | X ω ≤ c} := by
      apply measureReal_mono
      · intro ω hω
        change X ω < c at hω
        exact le_of_lt hω
      · exact measure_ne_top μ _
    _ ≤ Real.exp (-(-s) * c) * mgf X μ (-s) := h_closed
    _ = Real.exp (s * c) * ∫ ω, Real.exp (-s * X ω) ∂μ := by
      simp only [neg_neg, mgf]

/-! ## Matrix-row assembly -/

/--
The strict negative-argument MGF bound for independent sparse rows, expressed
entirely over the finite sparse matrix PMF. The row factors are intentionally
arbitrary; the scalar certificate analysis supplies their bounds.
-/
theorem sparseRademacherMatrix_strictNegativeMGF
    (m d : ℕ) (f : Fin m → (Fin d → ℤ) → ℝ)
    (s c : ℝ) (hs : 0 < s) :
    (sparseRademacherMatrix m d).toMeasure.real
        {J | ∑ j, f j (J j) < c} ≤
      Real.exp (s * c) *
        ∏ j, ∫ row, Real.exp (-s * f j row) ∂(sparseRademacherRow d).toMeasure := by
  have h_integrable :
      Integrable (fun J => Real.exp (-s * ∑ j, f j (J j)))
        (sparseRademacherMatrix m d).toMeasure := by
    rw [sparseRademacherMatrix_eq_map_uniformSeed]
    rw [← PMF.toMeasure_map
      (p := PMF.uniformOfFintype (SparseSeed m d))
      (f := sparseMatrix) (measurable_of_finite sparseMatrix)]
    apply (integrable_map_measure
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_finite sparseMatrix).aemeasurable).2
    exact Integrable.of_finite
  have h_markov :=
    strictExponentialMarkov
      (μ := (sparseRademacherMatrix m d).toMeasure)
      (X := fun J => ∑ j, f j (J j)) s c hs h_integrable
  calc
    (sparseRademacherMatrix m d).toMeasure.real
          {J | ∑ j, f j (J j) < c} ≤
        Real.exp (s * c) *
          ∫ J, Real.exp (-s * ∑ j, f j (J j)) ∂
            (sparseRademacherMatrix m d).toMeasure := h_markov
    _ = Real.exp (s * c) *
          ∫ J, ∏ j, Real.exp (-s * f j (J j)) ∂
            (sparseRademacherMatrix m d).toMeasure := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with J
      rw [Finset.mul_sum, Real.exp_sum]
    _ = Real.exp (s * c) *
          ∏ j, ∫ row, Real.exp (-s * f j row) ∂
            (sparseRademacherRow d).toMeasure := by
      congr 1
      exact sparseRademacherMatrix_integral_prod m d
        (fun j row => Real.exp (-s * f j row))

/--
The same bound at the public `eventProbability` boundary. This is the
finite-PMF bridge used by the modular lower-tail theorem; the
analytic bound remains a real inequality while the statement retains the
extended-real probability semantics.
-/
theorem sparseRademacherMatrix_eventProbability_toReal_strictNegativeMGF
    (m d : ℕ) (f : Fin m → (Fin d → ℤ) → ℝ)
    (s c : ℝ) (hs : 0 < s) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => ∑ j, f j (J j) < c)).toReal ≤
      Real.exp (s * c) *
        ∏ j, ∫ row, Real.exp (-s * f j row) ∂(sparseRademacherRow d).toMeasure := by
  rw [eventProbability_eq_toMeasure]
  exact sparseRademacherMatrix_strictNegativeMGF m d f s c hs

/-! ## Generalized Hölder -/

/--
Finite-product generalized Hölder in the nonnegative extended-real form.

The exponents are represented by nonnegative real weights summing to one,
which is the form needed after setting a weight to the reciprocal of each
finite Hölder exponent. The theorem is a direct wrapper around Mathlib's
finite-family inequality, so no scalar or certificate data is hidden here.
-/
theorem generalizedHolder
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (Y : ι → Ω → ℝ≥0∞) (p : ι → ℝ)
    (hY : ∀ i, AEMeasurable (Y i) μ)
    (hp : ∑ i, p i = 1)
    (hp_nonneg : ∀ i, 0 ≤ p i) :
    ∫⁻ ω, ∏ i, Y i ω ^ p i ∂μ ≤
      ∏ i, (∫⁻ ω, Y i ω ∂μ) ^ p i := by
  simpa using
    (ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ
      (fun i _ => hY i) (by simpa using hp)
      (fun i _ => hp_nonneg i))

end CertifiedProjections
