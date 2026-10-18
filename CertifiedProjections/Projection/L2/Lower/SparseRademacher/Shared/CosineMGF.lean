/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Analysis.SmoothBounds.NegativeMGF
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.GaussianFourier
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.MomentCore
import CertifiedProjections.Model.Vectors.Real
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Sparse scalar reduction: the Hölder boundary

The paper reduces a sparse-row negative-argument MGF to weighted
Gaussian cosine moments.  This file proves the Hölder part of that reduction
in isolation, and the final `sparseScalarReduction` declaration composes it
with the finite-PMF Fourier identity.  The support-indexed helpers remain
independent of the row bridge; no Fourier or certificate fact is hidden in
the Hölder interface.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

/-- The Gaussian factor with the reciprocal Hölder exponent exposed. -/
noncomputable def gaussianCosineHolderFactor
    (s x : ℝ) (G : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (|Real.cos (Real.sqrt (s / (2 / x)) * G)| ^ (2 / x))

/--
Generalized Hölder reduces the cosine product to the scalar moments
`F_s(2/x_i)`.  The positivity assumption on every `x_i` is deliberate: zero
coordinates are removed before applying this theorem, so no undefined
reciprocal exponent is silently introduced.
-/
theorem sparseScalarHolder
    {d : ℕ} (a : Fin d → ℝ) (s : ℝ)
    (ha : ∑ i, a i ^ 2 = 1)
    (hapos : ∀ i, 0 < a i ^ 2) :
    ∫⁻ G : ℝ,
        ∏ i, gaussianCosineHolderFactor s (a i ^ 2) G ^ (a i ^ 2)
          ∂(gaussianReal 0 1) ≤
      ∏ i, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2) := by
  let Y : Fin d → ℝ → ℝ≥0∞ :=
    fun i G => gaussianCosineHolderFactor s (a i ^ 2) G
  have hY : ∀ i, AEMeasurable (Y i) (gaussianReal 0 1) := by
    intro i
    dsimp [Y, gaussianCosineHolderFactor]
    fun_prop
  have hp : ∑ i, a i ^ 2 = 1 := ha
  have hp_nonneg : ∀ i, 0 ≤ a i ^ 2 := fun i => (hapos i).le
  have h := generalizedHolder Y (fun i => a i ^ 2) hY hp hp_nonneg
  simpa [Y, gaussianCosineHolderFactor, gaussianCosineMoment] using h

/-- Positive reciprocal Hölder exponents are at least two. -/
theorem reciprocalHolderExponent_ge_two
    {x : ℝ} (hx : 0 < x) (hx_le_one : x ≤ 1) :
    2 ≤ 2 / x := by
  exact (le_div_iff₀ hx).2 (by nlinarith)

/--
The weighted Hölder factor is exactly the cosine-square factor appearing in
the Gaussian Fourier product.  The coefficient is taken nonnegative here;
the later row-symmetry bridge handles coefficient signs separately.
-/
theorem gaussianCosineHolderFactor_rpow_eq_cos_sq
    {s x a G : ℝ} (hx : 0 < x) (ha : 0 ≤ a)
    (hax : a ^ 2 = x) :
    gaussianCosineHolderFactor s x G ^ x =
      ENNReal.ofReal (Real.cos (Real.sqrt (s / 2) * G * a) ^ 2) := by
  have hxne : x ≠ 0 := hx.ne'
  have harg : s / (2 / x) = (s / 2) * a ^ 2 := by
    rw [hax]
    field_simp
  have hsqrt : Real.sqrt (s / (2 / x)) = Real.sqrt (s / 2) * a := by
    rw [harg, Real.sqrt_mul' (s / 2) (sq_nonneg a), Real.sqrt_sq ha]
  dsimp [gaussianCosineHolderFactor]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (Real.rpow_nonneg (abs_nonneg _) _) hx.le]
  congr 1
  rw [← Real.rpow_mul (abs_nonneg _)]
  have hpow : (2 / x) * x = (2 : ℝ) := by
    field_simp
  rw [hpow, Real.rpow_two, hsqrt, sq_abs]
  congr 1
  ring_nf

/-!
The finite Gaussian Fourier product is now connected to the weighted
Hölder factors.  The coefficient signs are intentionally handled by a later
row-symmetry lemma; keeping this bridge nonnegative makes the exact
`sqrt (2*s) = 2 * sqrt (s/2)` normalization visible at the interface.
-/
theorem gaussianCosineProduct_holder
    {d : ℕ} (a : Fin d → ℝ) (s : ℝ)
    (ha : ∑ i, a i ^ 2 = 1)
    (hapos : ∀ i, 0 < a i ^ 2)
    (hanonneg : ∀ i, 0 ≤ a i) :
    ∫⁻ G : ℝ,
        ENNReal.ofReal
          (∏ i, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2)
          ∂(gaussianReal 0 1) ≤
      ∏ i, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2) := by
  have hsqrt : Real.sqrt (2 * s) = 2 * Real.sqrt (s / 2) := by
    calc
      Real.sqrt (2 * s) = Real.sqrt (4 * (s / 2)) := by
        congr 1
        ring
      _ = Real.sqrt 4 * Real.sqrt (s / 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt (s / 2) := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
            Real.sqrt_nonneg (4 : ℝ)]
        rw [hsqrt4]
  have hhalf (i : Fin d) (G : ℝ) :
      (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2 =
        Real.cos (Real.sqrt (s / 2) * G * a i) ^ 2 := by
    rw [hsqrt, Real.cos_sq]
    ring_nf
  have hpoint (G : ℝ) :
      ENNReal.ofReal
          (∏ i, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2) =
        ∏ i, gaussianCosineHolderFactor s (a i ^ 2) G ^ (a i ^ 2) := by
    rw [ENNReal.ofReal_prod_of_nonneg]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [hhalf i G]
      rw [gaussianCosineHolderFactor_rpow_eq_cos_sq
        (hapos i) (hanonneg i) rfl]
    · intro i hi
      rw [hhalf i G]
      positivity
  calc
    ∫⁻ G : ℝ,
        ENNReal.ofReal
          (∏ i, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2)
          ∂(gaussianReal 0 1) =
      ∫⁻ G : ℝ,
        ∏ i, gaussianCosineHolderFactor s (a i ^ 2) G ^ (a i ^ 2)
          ∂(gaussianReal 0 1) := by
      apply lintegral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ ≤ ∏ i, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2) :=
      sparseScalarHolder a s ha hapos

/-! ## Support-indexed scalar reduction -/

/-- The Hölder step with an explicit finite support, as used by (L4). -/
theorem sparseScalarHolder_on_finset
    {d : ℕ} (a : Fin d → ℝ) (s : ℝ) (S : Finset (Fin d))
    (hS : ∑ i ∈ S, a i ^ 2 = 1)
    (hapos : ∀ i ∈ S, 0 < a i ^ 2) :
    ∫⁻ G : ℝ,
        ∏ i ∈ S, gaussianCosineHolderFactor s (a i ^ 2) G ^ (a i ^ 2)
          ∂(gaussianReal 0 1) ≤
      ∏ i ∈ S, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2) := by
  let Y : Fin d → ℝ → ℝ≥0∞ :=
    fun i G => gaussianCosineHolderFactor s (a i ^ 2) G
  have hY : ∀ i, AEMeasurable (Y i) (gaussianReal 0 1) := by
    intro i
    dsimp [Y, gaussianCosineHolderFactor]
    fun_prop
  have h := ENNReal.lintegral_prod_norm_pow_le
    (μ := gaussianReal 0 1) S
    (fun i _ => hY i)
    (by simpa using hS)
    (fun i hi => (hapos i hi).le)
  simpa [Y, gaussianCosineHolderFactor, gaussianCosineMoment] using h

/-- The cosine product Hölder bound with zeros removed before reciprocation. -/
theorem gaussianCosineProduct_holder_on_finset
    {d : ℕ} (a : Fin d → ℝ) (s : ℝ) (S : Finset (Fin d))
    (hS : ∑ i ∈ S, a i ^ 2 = 1)
    (hapos : ∀ i ∈ S, 0 < a i ^ 2)
    (hanonneg : ∀ i ∈ S, 0 ≤ a i) :
    ∫⁻ G : ℝ,
        ENNReal.ofReal
          (∏ i ∈ S, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2)
          ∂(gaussianReal 0 1) ≤
      ∏ i ∈ S, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2) := by
  have hsqrt : Real.sqrt (2 * s) = 2 * Real.sqrt (s / 2) := by
    calc
      Real.sqrt (2 * s) = Real.sqrt (4 * (s / 2)) := by
        congr 1
        ring
      _ = Real.sqrt 4 * Real.sqrt (s / 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt (s / 2) := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
            Real.sqrt_nonneg (4 : ℝ)]
        rw [hsqrt4]
  have hhalf (i : Fin d) (G : ℝ) :
      (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2 =
        Real.cos (Real.sqrt (s / 2) * G * a i) ^ 2 := by
    rw [hsqrt, Real.cos_sq]
    ring_nf
  have hpoint (G : ℝ) :
      ENNReal.ofReal
          (∏ i ∈ S, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2) =
        ∏ i ∈ S, gaussianCosineHolderFactor s (a i ^ 2) G ^ (a i ^ 2) := by
    rw [ENNReal.ofReal_prod_of_nonneg]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [hhalf i G]
      rw [gaussianCosineHolderFactor_rpow_eq_cos_sq
        (hapos i hi) (hanonneg i hi) rfl]
    · intro i hi
      rw [hhalf i G]
      positivity
  calc
    ∫⁻ G : ℝ,
        ENNReal.ofReal
          (∏ i ∈ S, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2)
          ∂(gaussianReal 0 1) =
      ∫⁻ G : ℝ,
        ∏ i ∈ S, gaussianCosineHolderFactor s (a i ^ 2) G ^ (a i ^ 2)
          ∂(gaussianReal 0 1) := by
      apply lintegral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ ≤ ∏ i ∈ S, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2) :=
      sparseScalarHolder_on_finset a s S hS hapos

/--
The exact L4 sparse-scalar reduction. The support hypothesis is explicit so
zero coordinates are removed before the reciprocal Hölder exponents are
formed; coefficient signs are removed only by the evenness of cosine.
-/
theorem sparseScalarReduction
    {d : ℕ} (s : ℝ) (a : Fin d → ℝ) (S : Finset (Fin d))
    (hS : ∀ i, i ∈ S ↔ a i ≠ 0)
    (hs : 0 ≤ s)
    (ha : ∑ i, a i ^ 2 = 1) :
    ENNReal.ofReal
        (∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ∏ i ∈ S, gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2) := by
  classical
  let b : Fin d → ℝ := fun i => |a i|
  have hsum_b : ∑ i ∈ S, b i ^ 2 = 1 := by
    calc
      ∑ i ∈ S, b i ^ 2 = ∑ i, b i ^ 2 := by
        apply Finset.sum_subset
        · simp
        · intro i hi hnot
          have hzero : a i = 0 := by
            by_contra hne
            exact hnot ((hS i).2 hne)
          simp [b, hzero]
      _ = ∑ i, a i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [b]
      _ = 1 := ha
  have hapos_b : ∀ i ∈ S, 0 < b i ^ 2 := by
    intro i hi
    have hne : a i ≠ 0 := (hS i).1 hi
    have hbpos : 0 < b i := by
      exact abs_pos.mpr hne
    positivity
  have hsqrt : Real.sqrt (2 * s) = 2 * Real.sqrt (s / 2) := by
    calc
      Real.sqrt (2 * s) = Real.sqrt (4 * (s / 2)) := by
        congr 1
        ring
      _ = Real.sqrt 4 * Real.sqrt (s / 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt (s / 2) := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
            Real.sqrt_nonneg (4 : ℝ)]
        rw [hsqrt4]
  have hhalf (i : Fin d) (G : ℝ) :
      (1 + Real.cos (Real.sqrt (2 * s) * G * b i)) / 2 =
        Real.cos (Real.sqrt (s / 2) * G * b i) ^ 2 := by
    rw [hsqrt, Real.cos_sq]
    ring_nf
  have hfactor_abs (i : Fin d) (G : ℝ) :
      (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2 =
        (1 + Real.cos (Real.sqrt (2 * s) * G * b i)) / 2 := by
    by_cases h : 0 ≤ a i
    · simp [b, abs_of_nonneg h]
    · have h' : a i ≤ 0 := le_of_not_ge h
      simp only [b, abs_of_nonpos h']
      congr 2
      rw [show Real.sqrt (2 * s) * G * -a i =
        -(Real.sqrt (2 * s) * G * a i) by ring, Real.cos_neg]
  have hholder_factor (i : Fin d) (hi : i ∈ S) (G : ℝ) :
      ENNReal.ofReal
          ((1 + Real.cos (Real.sqrt (2 * s) * G * b i)) / 2) =
        gaussianCosineHolderFactor s (b i ^ 2) G ^ (b i ^ 2) := by
    have hpos : 0 < b i ^ 2 := hapos_b i hi
    rw [hhalf i G]
    exact (gaussianCosineHolderFactor_rpow_eq_cos_sq
      (s := s) (x := b i ^ 2) (a := b i) (G := G)
      hpos (by dsimp [b]; exact abs_nonneg _) rfl).symm
  let fG : ℝ → ℝ := fun G =>
    ∏ i, (1 + Real.cos (Real.sqrt (2 * s) * G * a i)) / 2
  have hf_meas : Measurable fG := by
    dsimp [fG]
    fun_prop
  have hf_integrable : Integrable fG (gaussianReal 0 1) := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 ?_
    filter_upwards [] with G
    have hnonneg : 0 ≤ fG G := by
      dsimp [fG]
      apply Finset.prod_nonneg
      intro i hi
      linarith [Real.neg_one_le_cos (Real.sqrt (2 * s) * G * a i)]
    have hle : fG G ≤ 1 := by
      dsimp [fG]
      apply Finset.prod_le_one
      · intro i hi
        linarith [Real.neg_one_le_cos (Real.sqrt (2 * s) * G * a i)]
      · intro i hi
        linarith [Real.cos_le_one (Real.sqrt (2 * s) * G * a i)]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hofreal :
      ENNReal.ofReal (∫ G, fG G ∂(gaussianReal 0 1)) =
        ∫⁻ G, ENNReal.ofReal (fG G) ∂(gaussianReal 0 1) :=
    ofReal_integral_eq_lintegral_ofReal hf_integrable
      (Filter.Eventually.of_forall (fun G => by
        dsimp [fG]
        apply Finset.prod_nonneg
        intro i hi
        linarith [Real.neg_one_le_cos (Real.sqrt (2 * s) * G * a i)]))
  have hpoint (G : ℝ) :
      ENNReal.ofReal (fG G) =
        ∏ i ∈ S, gaussianCosineHolderFactor s (b i ^ 2) G ^ (b i ^ 2) := by
    have hprod_abs :
        fG G = ∏ i, (1 + Real.cos (Real.sqrt (2 * s) * G * b i)) / 2 := by
      dsimp [fG]
      apply Finset.prod_congr rfl
      intro i hi
      exact hfactor_abs i G
    rw [hprod_abs, ENNReal.ofReal_prod_of_nonneg]
    · calc
        (∏ i, ENNReal.ofReal
            ((1 + Real.cos (Real.sqrt (2 * s) * G * b i)) / 2)) =
            ∏ i ∈ S, ENNReal.ofReal
              ((1 + Real.cos (Real.sqrt (2 * s) * G * b i)) / 2) := by
          symm
          apply Finset.prod_subset
          · simp
          · intro i hi hnot
            have hzero : a i = 0 := by
              by_contra hne
              exact hnot ((hS i).2 hne)
            simp [b, hzero]
        _ = ∏ i ∈ S, gaussianCosineHolderFactor s (b i ^ 2) G ^ (b i ^ 2) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hholder_factor i hi G
    · intro i hi
      linarith [Real.neg_one_le_cos (Real.sqrt (2 * s) * G * b i)]
  have hfour := sparseRow_negativeMGF_fourier d s a hs
  calc
    ENNReal.ofReal
        (∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) =
      ENNReal.ofReal (∫ G, fG G ∂(gaussianReal 0 1)) := by
        rw [hfour]
    _ = ∫⁻ G, ENNReal.ofReal (fG G) ∂(gaussianReal 0 1) := hofreal
    _ = ∫⁻ G,
        ∏ i ∈ S, gaussianCosineHolderFactor s (b i ^ 2) G ^ (b i ^ 2)
          ∂(gaussianReal 0 1) := by
      apply lintegral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ ≤ ∏ i ∈ S,
        gaussianCosineMoment s (2 / (b i ^ 2)) ^ (b i ^ 2) :=
      sparseScalarHolder_on_finset b s S hsum_b hapos_b
    _ = ∏ i ∈ S,
        gaussianCosineMoment s (2 / (a i ^ 2)) ^ (a i ^ 2) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [b]

end CertifiedProjections
