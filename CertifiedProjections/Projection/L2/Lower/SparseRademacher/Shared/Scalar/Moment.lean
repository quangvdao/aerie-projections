/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.MomentCore
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# The real sparse scalar moment

This module is the paper-facing real presentation of the existing ENNReal
Gaussian cosine moment.  The ENNReal object remains the one consumed by the
finite Hölder theorem; `sparseScalarF` is connected to it by a proved bridge.
Keeping the two presentations separate makes the later logarithmic
interpolation and lobe estimates independent of the finite-PMF reduction.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

/-- The real scalar integrand, with the `Real.rpow` convention explicit. -/
noncomputable def sparseScalarFIntegrand (s p G : ℝ) : ℝ :=
  Real.rpow |Real.cos (Real.sqrt (s / p) * G)| p

/--
The paper's real scalar moment

`F_s(p) = ∫ |cos (sqrt (s / p) G)|^p dγ(G)`.

The exponent is explicitly `Real.rpow`; the consumer theorems below require
`0 < p`, so the zero-exponent convention is never used implicitly.
-/
noncomputable def sparseScalarF (s p : ℝ) : ℝ :=
  ∫ G : ℝ, sparseScalarFIntegrand s p G ∂(gaussianReal 0 1)

private lemma sparseScalarF_measurable {s p : ℝ} (hp : 0 ≤ p) :
    Measurable (fun G : ℝ => sparseScalarFIntegrand s p G) := by
  have hbase : Continuous (fun G : ℝ =>
      |Real.cos (Real.sqrt (s / p) * G)|) := by
    fun_prop
  exact (hbase.rpow_const (fun _ => Or.inr hp)).measurable

private lemma sparseScalarF_ae_nonneg {s p : ℝ} :
    0 ≤ᵐ[gaussianReal 0 1] (fun G : ℝ => sparseScalarFIntegrand s p G) := by
  filter_upwards [] with G
  exact Real.rpow_nonneg (abs_nonneg _) _

private lemma sparseScalarF_ae_le_one {s p : ℝ} (hp : 0 < p) :
    (fun G : ℝ => sparseScalarFIntegrand s p G)
      ≤ᵐ[gaussianReal 0 1] (fun _ => (1 : ℝ)) := by
  filter_upwards [] with G
  exact Real.rpow_le_one (abs_nonneg _)
    (Real.abs_cos_le_one _) hp.le

/-- The real scalar integrand is integrable for every positive exponent. -/
theorem sparseScalarF_integrable {s p : ℝ} (hp : 0 < p) :
    Integrable (fun G : ℝ => sparseScalarFIntegrand s p G)
      (gaussianReal 0 1) := by
  refine Integrable.of_bound
    (sparseScalarF_measurable hp.le).aestronglyMeasurable 1 ?_
  filter_upwards [] with G
  have hnonneg : 0 ≤ sparseScalarFIntegrand s p G :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hle : sparseScalarFIntegrand s p G ≤ 1 :=
    Real.rpow_le_one (abs_nonneg _)
      (Real.abs_cos_le_one _) hp.le
  change |sparseScalarFIntegrand s p G| ≤ 1
  rw [abs_of_nonneg hnonneg]
  exact hle

/-- `F_s(p)` is nonnegative for every exponent. -/
theorem sparseScalarF_nonneg {s p : ℝ} :
    0 ≤ sparseScalarF s p := by
  exact integral_nonneg_of_ae sparseScalarF_ae_nonneg

/-- `F_s(p)` is at most one for every positive exponent. -/
theorem sparseScalarF_le_one {s p : ℝ} (hp : 0 < p) :
    sparseScalarF s p ≤ 1 := by
  have hfi := sparseScalarF_integrable (s := s) (p := p) hp
  calc
    sparseScalarF s p ≤
        ∫ _ : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) := by
      exact integral_mono_ae hfi (integrable_const 1)
        (sparseScalarF_ae_le_one hp)
    _ = 1 := by simp [integral_const]

/--
The real and ENNReal scalar moments are exactly the same object under
`ENNReal.ofReal`.
-/
theorem gaussianCosineMoment_eq_ofReal_sparseScalarF
    {s p : ℝ} (hp : 0 < p) :
    gaussianCosineMoment s p = ENNReal.ofReal (sparseScalarF s p) := by
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (sparseScalarF_integrable hp) sparseScalarF_ae_nonneg

end CertifiedProjections
