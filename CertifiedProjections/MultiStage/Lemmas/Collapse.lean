/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Stage
import CertifiedProjections.Probability.Finite.Counting
import CertifiedProjections.Probability.Product.RowTensorization
import Mathlib.Logic.Equiv.Prod

/-!
# Collapse of one stage

A stage collapses a table when it maps a table that is large at `τin` to one that is small at
`τout`. The main result is `stage_collapse_le`: if `μ.NoTwoConsecutiveBound ρ` holds and
`2 * (τout - 1) < τin`, a stage modulo `p` with `c` rows collapses a given table with probability at
most `ρ ^ c`.

Spec Lemma A.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}

/-- If `d` is congruent to `x` modulo `p`, then `centeredMod p x` has absolute value at most that of
`d`. -/
private theorem centered_natAbs_le {p : ℕ} {x d : ℤ}
    (h : (d : ZMod p) = x) : (centeredMod p x).natAbs ≤ d.natAbs := by
  by_cases hp : p = 0
  · subst p
    change d = x at h
    subst d
    exact le_rfl
  · let : NeZero p := ⟨hp⟩
    exact centeredMod_natAbs_le_of_intCast_eq h

/-- If `centeredMod p x` has absolute value at least `τin` and `2 * (τout - 1) < τin`, then
`centeredMod p (R + s * x)` and `centeredMod p (R + (s + 1) * x)` cannot both have absolute value
less than `τout`. -/
private theorem small_affine_no_consecutive {p τin τout : ℕ}
    (hτ : 2 * (τout - 1) < τin) {x : ℤ}
    (hx : τin ≤ (centeredMod p x).natAbs) (R s : ℤ)
    (hs : (centeredMod p (R + s * x)).natAbs < τout) :
    ¬ (centeredMod p (R + (s + 1) * x)).natAbs < τout := by
  intro hs'
  let d := centeredMod p (R + (s + 1) * x) - centeredMod p (R + s * x)
  have hd : (d : ZMod p) = x := by
    dsimp [d]
    push_cast
    simp only [centeredMod_intCast]
    push_cast
    ring
  have habs := centered_natAbs_le hd
  have hsub := Int.natAbs_sub_le (centeredMod p (R + (s + 1) * x))
    (centeredMod p (R + s * x))
  dsimp [d] at habs
  omega

/-- The dot product with `w` of the row `a` with entry `k` replaced by `z` is the sum of `a i * w i`
over `i ≠ k`, plus `z * w k`. -/
private theorem dot_update {f : ℕ} (a w : Fin f → ℤ) (k : Fin f) (z : ℤ) :
    (∑ i, Function.update a k z i * w i) =
      (∑ i ∈ Finset.univ.erase k, a i * w i) + z * w k := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- If `μ.NoTwoConsecutiveBound ρ` holds, `2 * (τout - 1) < τin`, and `X` is large at `τin`, then
the output of `stageMod p μ c X` is small at `τout` with probability at most `ρ ^ c`. Spec Lemma A,
for any entry law. The spec's hypothesis `τ_in ≤ (p + 1) / 2` is not needed. For `p > 0` it follows
from `hX`, because a table cannot be large at a threshold above `p / 2`. -/
theorem stage_collapse_le (μ : EntryLaw) {ρ : ℝ≥0∞} (hρ : μ.NoTwoConsecutiveBound ρ)
    {p τin τout : ℕ} (hτ : 2 * (τout - 1) < τin) (c : ℕ) (X : Table f F) (hX : IsLarge p τin X) :
    eventProbability (stageMod p μ c X) (fun Y => IsSmall p τout Y) ≤ ρ ^ c := by
  classical
  obtain ⟨k, φ, hx⟩ := hX
  let E : (Fin f → ℤ) → Prop :=
    fun a => (centeredMod p (∑ i, a i * X i φ)).natAbs < τout
  have hrow : eventProbability (μ.rowPMF f) E ≤ ρ := by
    apply EntryLaw.eventProbability_rowPMF_le μ k E ρ
    intro other
    let R := ∑ i ∈ Finset.univ.erase k, other i * X i φ
    have heq : eventProbability μ.entryPMF (fun z => E (Function.update other k z)) =
        eventProbability μ.entryPMF
          (fun z => (centeredMod p (R + z * X k φ)).natAbs < τout) := by
      apply eventProbability_congr
      intro z
      simp only [E, dot_update, R]
    rw [heq]
    exact hρ {z | (centeredMod p (R + z * X k φ)).natAbs < τout}
      (fun s hs => small_affine_no_consecutive hτ hx R s hs)
  have heq : eventProbability (stageMod p μ c X) (fun Y => IsSmall p τout Y) =
      eventProbability (μ.matrixPMF c f)
        (fun C => IsSmall p τout (ctr p (Matrix.of C * X))) := by
    unfold stageMod stage eventProbability
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  rw [heq]
  calc
    _ ≤ eventProbability (μ.matrixPMF c f) (fun C => ∀ j, E (C j)) := by
      apply eventProbability_mono
      intro C h j
      have hj := h j φ
      simpa only [E, ctr, Matrix.map_apply, centeredMod, ZMod.coe_valMinAbs,
        Matrix.mul_apply, Matrix.of_apply] using hj
    _ ≤ ρ ^ c := EntryLaw.eventProbability_matrixPMF_forall_le μ c f E ρ hrow

end CertifiedProjections.MultiStage
