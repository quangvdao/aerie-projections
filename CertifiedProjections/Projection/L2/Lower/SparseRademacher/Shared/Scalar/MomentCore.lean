/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The ENNReal Gaussian scalar moment core

This tiny module owns the ENNReal moment consumed by the finite generalized
Hölder proof.  Keeping it below both the finite-PMF reduction and the
paper-facing real scalar presentation prevents an import cycle when later
interpolation lemmas consume the real/ENNReal bridge.
-/

open scoped ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

/-- The ENNReal Gaussian-cosine moment used by the finite Hölder producer. -/
noncomputable def gaussianCosineMoment (s p : ℝ) : ℝ≥0∞ :=
  ∫⁻ G : ℝ,
    ENNReal.ofReal
      (|Real.cos (Real.sqrt (s / p) * G)| ^ p) ∂(gaussianReal 0 1)

end CertifiedProjections
