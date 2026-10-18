/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Modular.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Real vector interfaces

This module supplies the real dot products used by the analytic row bounds.
The public Euclidean interface uses `EuclideanSpace ℝ (Fin d)`, whose norm is
the `ℓ²` norm. Plain functions `Fin d → ℝ` instead inherit the `ℓ∞` norm and
must not be used with unqualified norm notation in JL statements.
-/

open scoped BigOperators

namespace CertifiedProjections

/-- The real dot product of an integer row with real coordinate weights. -/
def realRowDot {d : ℕ} (row : Fin d → ℤ) (w : Fin d → ℝ) : ℝ :=
  ∑ i, (row i : ℝ) * w i

/--
The integer matrix-row product becomes `realRowDot` after casting to `ℝ`.
-/
theorem intRowDot_cast_eq_realRowDot {m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) (j : Fin m) :
    (rowDot J w j : ℝ) = realRowDot (J j) (fun i => (w i : ℝ)) := by
  simp [rowDot, realRowDot]

/--
The real dot product against a coefficient vector carrying its canonical
Euclidean norm.
-/
def euclideanRowDot {d : ℕ} (row : Fin d → ℤ)
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  realRowDot row fun i => w i

@[simp]
theorem euclideanRowDot_zero {d : ℕ} (row : Fin d → ℤ) :
    euclideanRowDot row 0 = 0 := by
  simp [euclideanRowDot, realRowDot]

theorem euclideanRowDot_smul {d : ℕ} (row : Fin d → ℤ)
    (c : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    euclideanRowDot row (c • w) = c * euclideanRowDot row w := by
  simp only [euclideanRowDot, realRowDot, PiLp.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end CertifiedProjections
