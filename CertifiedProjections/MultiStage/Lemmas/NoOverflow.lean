/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Stage

/-!
# No overflow in one stage

The main result is `ctr_mul_eq_mul_ctr`: if the entries of the matrix `C` are bounded by `bound`,
the table `X` is small at `τ`, and the fan-in `f` satisfies `f * bound * (τ - 1) ≤ (p - 1) / 2`,
then `ctr p (C * X) = C * ctr p X`. The entries of the integer product `C * ctr p X` then have
absolute value at most `(p - 1) / 2`, so centering modulo `p` leaves it unchanged.

Spec Lemma B.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}

/-- If every entry of `C` has absolute value at most `bound`, `X` is small at `τ`, and
`f * bound * (τ - 1) ≤ (p - 1) / 2`, then `ctr p (C * X) = C * ctr p X`: centering the product gives
the integer product of `C` with the centered table. Spec Lemma B. -/
theorem ctr_mul_eq_mul_ctr {p τ bound : ℕ} (C : Matrix (Fin c) (Fin f) ℤ) (X : Table f F)
    (hC : ∀ i j, (C i j).natAbs ≤ bound) (hX : IsSmall p τ X)
    (hfan : f * bound * (τ - 1) ≤ (p - 1) / 2) :
    ctr p (C * X) = C * ctr p X := by
  classical
  by_cases hp : p = 0
  · subst p
    rfl
  · let _ : NeZero p := ⟨hp⟩
    ext i φ
    change centeredMod p (∑ j, C i j * X j φ) =
      ∑ j, C i j * centeredMod p (X j φ)
    apply (ZMod.valMinAbs_spec _ _).mpr
    constructor
    · push_cast
      apply Finset.sum_congr rfl
      intro j _
      rw [centeredMod_intCast]
    · have hbound : (∑ j, C i j * centeredMod p (X j φ)).natAbs ≤ (p - 1) / 2 := by
        calc
          _ ≤ ∑ j, (C i j * centeredMod p (X j φ)).natAbs :=
            Int.natAbs_sum_le _ _
          _ ≤ ∑ _j : Fin f, bound * (τ - 1) := by
            apply Finset.sum_le_sum
            intro j _
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul (hC i j) (by have := hX j φ; omega)
          _ = f * bound * (τ - 1) := by simp [Nat.mul_assoc]
          _ ≤ (p - 1) / 2 := hfan
      simp only [Set.mem_Ioc]
      have hp_pos : 0 < p := Nat.pos_of_ne_zero hp
      omega

end CertifiedProjections.MultiStage
