/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Modular.Centered
import Mathlib.Data.Matrix.Basic

/-!
# Integer projection squared norms

These definitions distinguish the squared norm of the source vector from the
squared norm of the whole projected vector. Every quantity is an exact natural
number obtained by summing squared integer magnitudes over all projection rows.
-/

open scoped BigOperators

namespace CertifiedProjections

/-- Integer dot product between row `j` of `J` and the source vector `w`. -/
def rowDot {rows d : ℕ} (J : Matrix (Fin rows) (Fin d) ℤ)
    (w : Fin d → ℤ) (j : Fin rows) : ℤ :=
  ∑ i, J j i * w i

/-- Natural squared norm of the unreduced projected vector `Jw`:
`∑ j, (rowDot J w j).natAbs ^ 2`. -/
def projectionSqNorm {rows d : ℕ}
    (J : Matrix (Fin rows) (Fin d) ℤ) (w : Fin d → ℤ) : ℕ :=
  ∑ j, (rowDot J w j).natAbs ^ 2

/-- Natural squared norm of `Jw` after centering each projected coordinate
modulo `q`: `∑ j, (centeredMod q (rowDot J w j)).natAbs ^ 2`. -/
def modularProjectionSqNorm (q : ℕ) {rows d : ℕ}
    (J : Matrix (Fin rows) (Fin d) ℤ) (w : Fin d → ℤ) : ℕ :=
  ∑ j, (centeredMod q (rowDot J w j)).natAbs ^ 2

/-- Natural squared norm after adding a row-wise integer shift and then
centering modulo `q`:
`∑ j, (centeredMod q (shift j + rowDot J w j)).natAbs ^ 2`.

This deterministic definition imposes no condition on `shift`. Tail statements
fix the shift before sampling the projection matrix. -/
def shiftedModularProjectionSqNorm (q : ℕ) {rows d : ℕ}
    (shift : Fin rows → ℤ) (J : Matrix (Fin rows) (Fin d) ℤ)
    (w : Fin d → ℤ) : ℕ :=
  ∑ j, (centeredMod q (shift j + rowDot J w j)).natAbs ^ 2

/-- A zero shift recovers the unshifted modular projected squared norm. -/
@[simp]
theorem shiftedModularProjectionSqNorm_zero (q : ℕ) {rows d : ℕ}
    (J : Matrix (Fin rows) (Fin d) ℤ) (w : Fin d → ℤ) :
    shiftedModularProjectionSqNorm q (fun _ => 0) J w =
      modularProjectionSqNorm q J w := by
  simp [shiftedModularProjectionSqNorm, modularProjectionSqNorm]

end CertifiedProjections
