/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Stage
import CertifiedProjections.Probability.Finite.Counting
import CertifiedProjections.Probability.Product.RowTensorization
import Mathlib.RingTheory.Int.Basic

/-!
# False zero in one stage

A stage produces a false zero when it maps a table that is nonzero mod `q` to one that is zero mod
`q`. The main result is `stage_zero_mod_le`: if `μ.AtomBound α` holds and `q` is a prime with
`2 * μ.bound < q`, a stage over ℤ with `c` rows produces a false zero on a given table with
probability at most `α ^ c`.

Spec Lemma 5.2.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}

/-- If `μ.AtomBound α` holds and all seed values that satisfy `E` are equal, then `E` has
probability at most `α` under `μ.entryPMF`. -/
private theorem entry_event_le_of_values_eq (μ : EntryLaw) {α : ℝ≥0∞}
    (hα : μ.AtomBound α) (E : ℤ → Prop)
    (huniq : ∀ s t : μ.Seed, E (μ.value s) → E (μ.value t) → μ.value s = μ.value t) :
    eventProbability μ.entryPMF E ≤ α := by
  classical
  let : MeasurableSpace μ.Seed := ⊤
  change eventProbability ((PMF.uniformOfFintype μ.Seed).map μ.value) E ≤ α
  unfold eventProbability
  rw [PMF.map_comp]
  change eventProbability (PMF.uniformOfFintype μ.Seed) (fun s => E (μ.value s)) ≤ α
  by_cases hex : ∃ s : μ.Seed, E (μ.value s)
  · obtain ⟨t, ht⟩ := hex
    refine (eventProbability_mono _ (fun s hs => huniq s t hs ht)).trans ?_
    have heq : eventProbability (PMF.uniformOfFintype μ.Seed)
        (fun s => μ.value s = μ.value t) = μ.entryPMF (μ.value t) := by
      rw [eventProbability_eq_sum, EntryLaw.entryPMF, PMF.map_apply, tsum_fintype]
      apply Finset.sum_congr rfl
      intro s _
      by_cases he : μ.value s = μ.value t
      · simp [he]
      · simp [he, Ne.symm he]
    rw [heq]
    exact hα _
  · have heq : eventProbability (PMF.uniformOfFintype μ.Seed)
        (fun s => E (μ.value s)) = 0 := by
      rw [eventProbability_congr _ (fun s => iff_false_intro (fun hs => hex ⟨s, hs⟩)),
        eventProbability_false]
    rw [heq]
    exact bot_le

/-- Let `μ.AtomBound α` hold, and let `q` be a prime with `2 * μ.bound < q` that does not divide
`w k`. Then for every choice `other` of the remaining entries of a row, the probability over the
entry `z` in position `k` that `q` divides the dot product of the row with `w` is at most `α`. -/
private theorem entry_zero_mod_le (μ : EntryLaw) {α : ℝ≥0∞} (hα : μ.AtomBound α)
    {q : ℕ} (hq : q.Prime) (hb : 2 * μ.bound < q) (w : Fin f → ℤ)
    (k : Fin f) (hk : ¬ (q : ℤ) ∣ w k) (other : Fin f → ℤ) :
    eventProbability μ.entryPMF
      (fun z => (q : ℤ) ∣ ∑ i, Function.update other k z i * w i) ≤ α := by
  classical
  apply entry_event_le_of_values_eq μ hα
  intro s t hs ht
  have hsub :
      (∑ i, Function.update other k (μ.value s) i * w i) -
        (∑ i, Function.update other k (μ.value t) i * w i) =
      (μ.value s - μ.value t) * w k := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · simp [sub_mul]
    · intro i _ hi
      simp [Function.update_of_ne hi]
    · simp
  have hdvd : (q : ℤ) ∣ (μ.value s - μ.value t) * w k := by
    rw [← hsub]
    exact dvd_sub hs ht
  have hprime : Prime (q : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  have hdvd' := (hprime.dvd_mul.mp hdvd).resolve_right hk
  have hsmall : (μ.value s - μ.value t).natAbs < (q : ℤ).natAbs := by
    have hdiff := Int.natAbs_sub_le (μ.value s) (μ.value t)
    have hsbound := μ.natAbs_value_le s
    have htbound := μ.natAbs_value_le t
    simpa only [Int.natAbs_natCast] using (by omega :
      (μ.value s - μ.value t).natAbs < q)
  exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd' hsmall)

/-- If `μ.AtomBound α` holds, `q` is a prime with `2 * μ.bound < q`, and `X` is nonzero mod `q`,
then the output of `stage μ c X` is zero mod `q` with probability at most `α ^ c`. Spec Lemma 5.2,
for any entry law with bounded atoms. -/
theorem stage_zero_mod_le (μ : EntryLaw) {α : ℝ≥0∞} (hα : μ.AtomBound α) {q : ℕ} (hq : q.Prime)
    (hb : 2 * μ.bound < q) (c : ℕ) (X : Table f F) (hX : ¬ ZeroMod q X) :
    eventProbability (stage μ c X) (ZeroMod q) ≤ α ^ c := by
  classical
  obtain ⟨k, φ, hk⟩ : ∃ k φ, ¬ (q : ℤ) ∣ X k φ := by
    simpa only [ZeroMod, not_forall] using hX
  have hrow : eventProbability (μ.rowPMF f)
      (fun a => (q : ℤ) ∣ ∑ i, a i * X i φ) ≤ α := by
    apply EntryLaw.eventProbability_rowPMF_le μ k
    intro other
    exact entry_zero_mod_le μ hα hq hb (fun i => X i φ) k hk other
  change eventProbability ((μ.matrixPMF c f).map (fun C => Matrix.of C * X))
      (ZeroMod q) ≤ α ^ c
  unfold eventProbability
  rw [PMF.map_comp]
  change eventProbability (μ.matrixPMF c f) (fun C => ZeroMod q (Matrix.of C * X)) ≤ α ^ c
  refine (eventProbability_mono _ (fun C hC => fun j => hC j φ)).trans ?_
  change eventProbability (μ.matrixPMF c f)
    (fun C => ∀ j, (q : ℤ) ∣ ∑ i, C j i * X i φ) ≤ α ^ c
  exact EntryLaw.eventProbability_matrixPMF_forall_le μ c f
    (fun a => (q : ℤ) ∣ ∑ i, a i * X i φ) α hrow

end CertifiedProjections.MultiStage
