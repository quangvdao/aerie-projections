/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Probability.Finite.Counting

/-!
# Expectations and event probabilities under a PMF

`expectation P g` is the `ℝ≥0∞`-valued expectation of `g` under a PMF `P`. The lemmas in this file
relate it to `eventProbability` and to the PMF operations `pure`, `map` and `bind`. They hold for
every type: none of them needs a countability or measurability assumption.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

/-- Expectation of an `ℝ≥0∞`-valued function under a PMF. -/
noncomputable def expectation {α : Type*} (P : PMF α) (g : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, P a * g a

open scoped Classical in
/-- The probability of an event is the sum of the masses of the points where it holds. -/
theorem eventProbability_eq_tsum {α : Type*} (P : PMF α) (E : α → Prop) :
    eventProbability P E = ∑' a, if E a then P a else 0 := by
  classical
  simp [eventProbability, PMF.map_apply]

/-- Every event has probability at most one. -/
theorem eventProbability_le_one {α : Type*} (P : PMF α) (E : α → Prop) :
    eventProbability P E ≤ 1 := PMF.coe_le_one _ _

/-- The probability of an event is the expectation of its indicator. -/
theorem eventProbability_eq_expectation {α : Type*} (P : PMF α) (E : α → Prop) [DecidablePred E] :
    eventProbability P E = expectation P (fun a => if E a then 1 else 0) := by
  classical
  simp [eventProbability, PMF.map_apply, expectation, mul_ite]

/-- If `E` implies `E'`, the probability of `E` is at most the probability of `E'`. -/
theorem eventProbability_mono_of_imp {α : Type*} (P : PMF α) {E E' : α → Prop}
    (h : ∀ a, E a → E' a) : eventProbability P E ≤ eventProbability P E' := by
  classical
  simp only [eventProbability_eq_expectation, expectation]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (by
    split_ifs with ha ha'
    · rfl
    · exact False.elim (ha' (h a ha))
    · exact bot_le
    · rfl) _

/-- If `E` implies `E'` on the support of `P`, the probability of `E` is at most the probability of
`E'`. -/
theorem eventProbability_mono_of_support {α : Type*} (P : PMF α) {E E' : α → Prop}
    (h : ∀ a ∈ P.support, E a → E' a) : eventProbability P E ≤ eventProbability P E' := by
  classical
  rw [eventProbability_eq_tsum, eventProbability_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ P.support
  · by_cases he : E a
    · simp [he, h a ha he]
    · simp [he]
  · have hz : P a = 0 := (P.apply_eq_zero_iff a).2 ha
    simp [hz]

/-- Union bound: if `E` implies `E₁` or `E₂`, the probability of `E` is at most the sum of the
probabilities of `E₁` and `E₂`. -/
theorem eventProbability_le_add {α : Type*} (P : PMF α)
    (E E₁ E₂ : α → Prop) (h : ∀ a, E a → E₁ a ∨ E₂ a) :
    eventProbability P E ≤ eventProbability P E₁ + eventProbability P E₂ := by
  classical
  simp only [eventProbability_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases hE : E a
  · rcases h a hE with h₁ | h₂
    · simp [hE, h₁]
    · simp [hE, h₂]
  · simp [hE]

/-- The probability that `E` fails is one minus the probability of `E`. -/
theorem eventProbability_not {α : Type*} (P : PMF α) (E : α → Prop) :
    eventProbability P (fun a => ¬ E a) = 1 - eventProbability P E := by
  classical
  have hadd : eventProbability P (fun a => ¬ E a) + eventProbability P E = 1 := by
    rw [eventProbability_eq_tsum, eventProbability_eq_tsum, ← ENNReal.tsum_add]
    convert P.tsum_coe using 1
    congr 1
    funext a
    by_cases h : E a <;> simp [h]
  exact (ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
    (eventProbability_le_one P E)) hadd)

/-- The false event has probability zero. -/
theorem eventProbability_false_eq_zero {α : Type*} (P : PMF α) :
    eventProbability P (fun _ => False) = 0 := by
  classical
  simp [eventProbability, PMF.map_apply]

/-- The probability of `E` under `P.map f` is the probability under `P` that `f a` satisfies `E`. -/
theorem eventProbability_map {α β : Type*} (P : PMF α) (f : α → β) (E : β → Prop) :
    eventProbability (P.map f) E = eventProbability P (fun a => E (f a)) := by
  simp [eventProbability, PMF.map_comp]

/-- The probability of `E` under `P.bind K` is the expectation over `P` of the probability of `E`
under `K a`. -/
theorem eventProbability_bind {α β : Type*} (P : PMF α) (K : α → PMF β) (E : β → Prop) :
    eventProbability (P.bind K) E = expectation P (fun a => eventProbability (K a) E) := by
  classical
  simp only [eventProbability_eq_expectation, expectation, PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

/-- Markov's inequality: if `g` is at least `d` wherever `E` holds on the support of `P`, the
probability of `E` is at most the expectation of `g` divided by `d`. -/
theorem eventProbability_le_expectation_div {α : Type*} (P : PMF α)
    (E : α → Prop) (g : α → ℝ≥0∞) (d : ℝ≥0∞) (hd₀ : d ≠ 0) (hd_top : d ≠ ∞)
    (h : ∀ a ∈ P.support, E a → d ≤ g a) :
    eventProbability P E ≤ expectation P g / d := by
  classical
  apply (ENNReal.le_div_iff_mul_le (Or.inl hd₀) (Or.inl hd_top)).mpr
  rw [eventProbability_eq_tsum, ← ENNReal.tsum_mul_right]
  unfold expectation
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ P.support
  · by_cases hE : E a
    · simpa [hE] using mul_le_mul' (le_refl (P a)) (h a ha hE)
    · simp [hE]
  · have hz : P a = 0 := (P.apply_eq_zero_iff a).mpr ha
    simp [hz]

/-- The expectation of `u` under the law concentrated at `a` is `u a`. -/
theorem expectation_pure {α : Type*} (a : α) (u : α → ℝ≥0∞) :
    expectation (PMF.pure a) u = u a := by
  classical
  simp [expectation, PMF.pure_apply]

/-- The expectation of `u` under `P.bind Q` is the expectation over `P` of the expectation of `u`
under `Q a`. -/
theorem expectation_bind {α β : Type*} (P : PMF α) (Q : α → PMF β)
    (u : β → ℝ≥0∞) :
    expectation (P.bind Q) u = expectation P (fun a => expectation (Q a) u) := by
  unfold expectation
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

/-- The expectation of `u` under `P.map v` is the expectation under `P` of `u ∘ v`. -/
theorem expectation_map {α β : Type*} (P : PMF α) (v : α → β)
    (u : β → ℝ≥0∞) : expectation (P.map v) u = expectation P (fun a => u (v a)) := by
  rw [PMF.map, expectation_bind]
  simp only [Function.comp_apply, expectation_pure]

/-- If `g ≤ h` pointwise, the expectation of `g` is at most the expectation of `h`. -/
theorem expectation_mono {α : Type*} (P : PMF α) {g h : α → ℝ≥0∞}
    (hgh : ∀ a, g a ≤ h a) : expectation P g ≤ expectation P h :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hgh a) _

/-- The expectation of a constant is that constant. -/
theorem expectation_const {α : Type*} (P : PMF α) (v : ℝ≥0∞) :
    expectation P (fun _ => v) = v := by
  simp [expectation, ENNReal.tsum_mul_right, P.tsum_coe]

/-- A constant factor can be taken outside an expectation. -/
theorem expectation_const_mul {α : Type*} (P : PMF α) (a : ℝ≥0∞)
    (u : α → ℝ≥0∞) : expectation P (fun x => a * u x) = a * expectation P u := by
  unfold expectation
  simp_rw [mul_left_comm (P _) a, ENNReal.tsum_mul_left]

/-- The expectation of a finite sum is the sum of the expectations. -/
theorem expectation_finset_sum {α ι : Type*} (P : PMF α) (s : Finset ι)
    (u : ι → α → ℝ≥0∞) :
    expectation P (fun x => ∑ i ∈ s, u i x) = ∑ i ∈ s, expectation P (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectation]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    unfold expectation at *
    simp_rw [mul_add, ENNReal.tsum_add]
    rw [ih]

/-- The expectation under the uniform law on a finite type is the average of the values. -/
theorem expectation_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α]
    (g : α → ℝ≥0∞) :
    expectation (PMF.uniformOfFintype α) g =
      (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, g a := by
  simp [expectation, PMF.uniformOfFintype_apply, tsum_fintype, Finset.mul_sum]

end CertifiedProjections.MultiStage
