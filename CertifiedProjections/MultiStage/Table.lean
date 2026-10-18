/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Modular.Projection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Real.Basic

/-!
# Integer tables

A `Table f F` is an integer matrix with `f` rows and `F` columns. This file defines the squared norm
(`sqNorm`), centering modulo `p` (`ctr`), the predicates `IsLarge` and `IsSmall` at a threshold `τ`,
divisibility of every entry by `q` (`ZeroMod`), re-indexing (`reshape`), stacking (`stack`) and
one-column tables (`colTable`), and proves how these operations interact (spec §2).
-/

open scoped BigOperators

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}

/-- An integer table with `f` rows and `F` columns. -/
abbrev Table (f F : ℕ) := Matrix (Fin f) (Fin F) ℤ

/-- The squared norm of `X`: the sum of the squares of its entries. -/
def sqNorm (X : Table f F) : ℕ := ∑ k, ∑ φ, (X k φ).natAbs ^ 2
/-- Center `X` modulo `p`: replace every entry `z` by `centeredMod p z`, the integer congruent to
`z` modulo `p` of smallest absolute value. For `p = 0` the table is unchanged. -/
def ctr (p : ℕ) (X : Table f F) : Table f F := X.map (centeredMod p)
/-- `X` is large at `τ`: some entry of `ctr p X` has absolute value at least `τ`. -/
def IsLarge (p τ : ℕ) (X : Table f F) : Prop := ∃ k φ, τ ≤ (centeredMod p (X k φ)).natAbs
/-- `X` is small at `τ`: every entry of `ctr p X` has absolute value less than `τ`. -/
def IsSmall (p τ : ℕ) (X : Table f F) : Prop := ∀ k φ, (centeredMod p (X k φ)).natAbs < τ
/-- `X` is zero mod `q`: every entry is divisible by `q`. -/
def ZeroMod (q : ℕ) (X : Table f F) : Prop := ∀ k φ, (q : ℤ) ∣ X k φ

/-- Re-index the entries of `X` along the bijection `e` of index pairs: the entry of `reshape e X`
at position `e (k, φ)` is `X k φ`. -/
def reshape (e : Fin f × Fin F ≃ Fin f' × Fin F') (X : Table f F) : Table f' F' :=
  Matrix.of fun k φ => X (e.symm (k, φ)).1 (e.symm (k, φ)).2
/-- Stack `g` tables with `c` rows each into one table with `g * c` rows (through
`finProdFinEquiv`). -/
def stack (T : Fin g → Table c F) : Table (g * c) F :=
  Matrix.of fun k φ => T (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 φ
/-- A vector as a one-column table. -/
def colTable (w : Fin f → ℤ) : Table f 1 := Matrix.of fun k _ => w k

variable {p q τ : ℕ} {X : Table f F} {e : Fin f × Fin F ≃ Fin f' × Fin F'} {T : Fin g → Table c F}

/-- A table is small at `τ` exactly when it is not large at `τ`. -/
theorem not_isLarge_iff_isSmall : ¬ IsLarge p τ X ↔ IsSmall p τ X := by
  simp only [IsLarge, IsSmall, not_exists, not_le]
/-- Centering a table twice has the same effect as centering once. -/
theorem ctr_ctr : ctr p (ctr p X) = ctr p X := by
  ext k φ
  simp [ctr, centeredMod]
/-- Centering cannot increase the squared norm. -/
theorem sqNorm_ctr_le : sqNorm (ctr p X) ≤ sqNorm X := by
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro φ _
  exact Nat.pow_le_pow_left (centeredMod_natAbs_le p (X k φ)) 2
/-- The squared norm vanishes exactly for the zero table. -/
theorem sqNorm_eq_zero_iff : sqNorm X = 0 ↔ X = 0 := by
  simp only [sqNorm, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    pow_eq_zero_iff (by decide : 2 ≠ 0), Int.natAbs_eq_zero]
  constructor
  · intro h
    ext k φ
    exact h k φ
  · intro h k φ
    simp [h]
/-- Casting the squared norm to the reals gives the sum of the squared real entries. -/
theorem sqNorm_cast_real (X : Table f F) :
    (sqNorm X : ℝ) = ∑ i, ∑ j, (X i j : ℝ) ^ 2 := by
  simp [sqNorm, Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-- Centering a table modulo zero leaves it unchanged. -/
theorem ctr_modulus_zero (Y : Table f F) : ctr 0 Y = Y := by
  ext k φ
  rfl

/-- Re-indexing preserves the squared norm. -/
theorem sqNorm_reshape : sqNorm (reshape e X) = sqNorm X := by
  unfold sqNorm reshape
  simp only [Matrix.of_apply]
  simpa only [Fintype.sum_prod_type] using
    e.symm.sum_comp (fun a => (X a.1 a.2).natAbs ^ 2)
/-- Centering commutes with re-indexing. -/
theorem ctr_reshape : ctr p (reshape e X) = reshape e (ctr p X) := by
  rfl
/-- A re-indexed table is large at `τ` exactly when the original table is. -/
theorem isLarge_reshape : IsLarge p τ (reshape e X) ↔ IsLarge p τ X := by
  constructor
  · rintro ⟨k, φ, h⟩
    exact ⟨(e.symm (k, φ)).1, (e.symm (k, φ)).2, h⟩
  · rintro ⟨k, φ, h⟩
    refine ⟨(e (k, φ)).1, (e (k, φ)).2, ?_⟩
    simpa [reshape] using h
/-- A re-indexed table is zero mod `q` exactly when the original table is. -/
theorem zeroMod_reshape : ZeroMod q (reshape e X) ↔ ZeroMod q X := by
  constructor
  · intro h k φ
    simpa [reshape] using h (e (k, φ)).1 (e (k, φ)).2
  · intro h k φ
    exact h (e.symm (k, φ)).1 (e.symm (k, φ)).2
/-- The squared norm of a stack is the sum of the squared norms. -/
theorem sqNorm_stack : sqNorm (stack T) = ∑ i, sqNorm (T i) := by
  unfold sqNorm stack
  simp only [Matrix.of_apply]
  simpa only [Fintype.sum_prod_type] using
    (finProdFinEquiv : Fin g × Fin c ≃ Fin (g * c)).symm.sum_comp
      (fun a => ∑ φ, (T a.1 a.2 φ).natAbs ^ 2)
/-- Centering commutes with stacking. -/
theorem ctr_stack : ctr p (stack T) = stack fun i => ctr p (T i) := by
  rfl
/-- A stack is small at `τ` exactly when each of its tables is. -/
theorem isSmall_stack : IsSmall p τ (stack T) ↔ ∀ i, IsSmall p τ (T i) := by
  constructor
  · intro h i k φ
    have h' := h (finProdFinEquiv (i, k)) φ
    change (centeredMod p
      (T (finProdFinEquiv.symm (finProdFinEquiv (i, k))).1
        (finProdFinEquiv.symm (finProdFinEquiv (i, k))).2 φ)).natAbs < τ at h'
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h k φ
    exact h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 φ
/-- A stack is zero mod `q` exactly when each of its tables is. -/
theorem zeroMod_stack : ZeroMod q (stack T) ↔ ∀ i, ZeroMod q (T i) := by
  constructor
  · intro h i k φ
    have h' := h (finProdFinEquiv (i, k)) φ
    change (q : ℤ) ∣ T (finProdFinEquiv.symm (finProdFinEquiv (i, k))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, k))).2 φ at h'
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h k φ
    exact h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 φ

end CertifiedProjections.MultiStage
