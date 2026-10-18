/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Probability.Finite.Experiment
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Uniform finite-function probability bridge

A uniform finite function is the finite product of its uniform coordinate
laws. This module proves that statement at the `PMF.toMeasure` boundary,
derives exact coordinate marginals and independence, and connects the
project's event probability with measure events and finite integrals.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

universe u v w

section UniformEquiv

variable {α : Type u} {β : Type v}
variable [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- A finite equivalence transports the uniform PMF to the uniform PMF. -/
theorem map_uniformOfFintype_equiv (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr e]
  calc
    (∑' a : α, if b = e a then
        (↑(Fintype.card β) : ENNReal)⁻¹ else 0) =
        ∑' b' : β, if b = b' then
          (↑(Fintype.card β) : ENNReal)⁻¹ else 0 :=
      e.tsum_eq (fun b' : β =>
        if b = b' then (↑(Fintype.card β) : ENNReal)⁻¹ else 0)
    _ = (↑(Fintype.card β) : ENNReal)⁻¹ := by simp

/--
Pull an event on a finite uniform space back along an equivalence without
changing its probability.
-/
theorem eventProbability_uniform_equiv (e : α ≃ β) (event : β → Prop) :
    eventProbability (PMF.uniformOfFintype β) event =
      eventProbability (PMF.uniformOfFintype α) (fun a => event (e a)) := by
  rw [← map_uniformOfFintype_equiv e]
  unfold eventProbability
  rw [PMF.map_comp]
  rfl

end UniformEquiv

section UniformPi

variable {ι : Type u} [Fintype ι]
variable (α : ι → Type v) [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]

/--
The generic uniform-function constructor agrees with Mathlib's uniform PMF
for any ambient finite enumeration.
-/
theorem uniformPiPMF_eq_uniformOfFintype
    [piFintype : Fintype ((i : ι) → α i)] :
    uniformPiPMF α = PMF.uniformOfFintype ((i : ι) → α i) := by
  apply PMF.ext
  intro x
  simp only [uniformPiPMF, PMF.uniformOfFintype_apply]
  congr 1
  exact_mod_cast
    (@Nat.card_eq_fintype_card ((i : ι) → α i)
      (Fintype.ofFinite ((i : ι) → α i))).symm.trans
        (@Nat.card_eq_fintype_card ((i : ι) → α i) piFintype)

variable [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]

/-- The uniform finite-function PMF is the product of its coordinate measures. -/
theorem uniformPiPMF_toMeasure :
    (uniformPiPMF α).toMeasure =
      Measure.pi (fun i => (PMF.uniformOfFintype (α i)).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)]
  rw [Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [uniformPiPMF, PMF.uniformOfFintype_apply]
  rw [← @Nat.card_eq_fintype_card ((i : ι) → α i)
    (Fintype.ofFinite ((i : ι) → α i)), Nat.card_pi]
  simp_rw [Nat.card_eq_fintype_card]
  rw [Nat.cast_prod]
  exact ENNReal.prod_inv_distrib (by
    intro i _ j _ _
    left
    simp)

/-- Every coordinate of a uniform finite function has the uniform marginal. -/
theorem uniformPiPMF_marginal (i : ι) :
    (uniformPiPMF α).map (fun x => x i) = PMF.uniformOfFintype (α i) := by
  classical
  apply PMF.ext
  intro a
  calc
    ((uniformPiPMF α).map (fun x => x i)) a =
        ((uniformPiPMF α).map (fun x => x i)).toMeasure {a} := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
    _ = (uniformPiPMF α).toMeasure ((fun x => x i) ⁻¹' {a}) := by
      rw [PMF.toMeasure_map_apply _ _ _ (measurable_pi_apply i)
        (measurableSet_singleton a)]
    _ = Measure.pi
          (fun j => (PMF.uniformOfFintype (α j)).toMeasure)
          ((fun x => x i) ⁻¹' {a}) := by
      rw [uniformPiPMF_toMeasure]
    _ = (Measure.pi
          (fun j => (PMF.uniformOfFintype (α j)).toMeasure)).map
          (fun x => x i) {a} := by
      rw [Measure.map_apply (measurable_pi_apply i)
        (measurableSet_singleton a)]
    _ = (PMF.uniformOfFintype (α i)).toMeasure {a} := by
      rw [(measurePreserving_eval
        (fun j => (PMF.uniformOfFintype (α j)).toMeasure) i).map_eq]
    _ = (PMF.uniformOfFintype (α i)) a := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]

end UniformPi

section IndependentUniformCoordinates

variable {ι : Type u} [Fintype ι]
variable {α : ι → Type v} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
variable {β : ι → Type w}

variable [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]

/-- The `i`-th mapped coordinate has the corresponding mapped marginal PMF. -/
theorem uniformPiMap_marginal
    (f : (i : ι) → α i → β i) (i : ι) :
    (uniformPiMap f).map (fun x => x i) =
      (PMF.uniformOfFintype (α i)).map (f i) := by
  classical
  calc
    (uniformPiMap f).map (fun x => x i) =
        (uniformPiPMF α).map (f i ∘ fun x => x i) := by
          rw [uniformPiMap, PMF.map_comp]
          rfl
    _ = ((uniformPiPMF α).map (fun x => x i)).map (f i) := by
          rw [PMF.map_comp]
    _ = (PMF.uniformOfFintype (α i)).map (f i) := by
          rw [uniformPiPMF_marginal]

variable [∀ i, MeasurableSpace (β i)]

/--
Coordinatewise images of a uniform finite function form the product of the
mapped coordinate measures.
-/
theorem uniformPiMap_toMeasure (f : (i : ι) → α i → β i)
    (hf : ∀ i, Measurable (f i)) :
    (uniformPiMap f).toMeasure =
      Measure.pi (fun i => ((PMF.uniformOfFintype (α i)).map (f i)).toMeasure) := by
  classical
  let g : ((i : ι) → α i) → ((i : ι) → β i) :=
    fun x i => f i (x i)
  have hg : Measurable g := measurable_pi_iff.mpr fun i =>
    (hf i).comp (measurable_pi_apply i)
  calc
    (uniformPiMap f).toMeasure =
        (uniformPiPMF α).toMeasure.map g := by
      rw [uniformPiMap]
      exact (PMF.toMeasure_map (p := uniformPiPMF α) (f := g) hg).symm
    _ = (Measure.pi
          (fun i => (PMF.uniformOfFintype (α i)).toMeasure)).map g := by
      rw [uniformPiPMF_toMeasure]
    _ = Measure.pi
          (fun i => (PMF.uniformOfFintype (α i)).toMeasure.map (f i)) := by
      exact Measure.pi_map_pi (fun i => (hf i).aemeasurable)
    _ = Measure.pi
          (fun i => ((PMF.uniformOfFintype (α i)).map (f i)).toMeasure) := by
      congr 1
      funext i
      exact PMF.toMeasure_map
        (p := PMF.uniformOfFintype (α i)) (f := f i) (hf i)

/-- Point masses of a coordinatewise image factor as a finite product. -/
theorem uniformPiMap_apply
    [∀ i, MeasurableSingletonClass (β i)]
    (f : (i : ι) → α i → β i)
    (hf : ∀ i, Measurable (f i)) (y : (i : ι) → β i) :
    uniformPiMap f y =
      ∏ i, ((PMF.uniformOfFintype (α i)).map (f i)) (y i) := by
  classical
  calc
    uniformPiMap f y =
        (uniformPiMap f).toMeasure {y} := by
      rw [PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton y)]
    _ = Measure.pi
          (fun i =>
            ((PMF.uniformOfFintype (α i)).map (f i)).toMeasure)
          {y} := by
      rw [uniformPiMap_toMeasure f hf]
    _ = ∏ i,
          ((PMF.uniformOfFintype (α i)).map (f i)).toMeasure
            {y i} := by
      rw [Measure.pi_singleton]
    _ = ∏ i,
          ((PMF.uniformOfFintype (α i)).map (f i)) (y i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton (y i))]

/-- The mapped coordinates are mutually independent. -/
theorem uniformPiMap_iIndep (f : (i : ι) → α i → β i)
    (hf : ∀ i, Measurable (f i)) :
    iIndepFun (fun i x => x i) (uniformPiMap f).toMeasure := by
  classical
  rw [uniformPiMap_toMeasure f hf]
  simpa using
    (iIndepFun_pi
      (μ := fun i => ((PMF.uniformOfFintype (α i)).map (f i)).toMeasure)
      (X := fun _ => id) (fun _ => aemeasurable_id))

end IndependentUniformCoordinates

section EventsAndIntegrals

variable {γ : Type u} [Countable γ] [MeasurableSpace γ]
  [MeasurableSingletonClass γ]

/--
Mapped experiments have the same event probability when their pulled-back
events agree pointwise. The result permits different output types.
-/
theorem eventProbability_map_congr
    {α β δ : Type*} (p : PMF α)
    (f : α → β) (g : α → δ)
    (event : β → Prop) (event' : δ → Prop)
    (h : ∀ x, event (f x) ↔ event' (g x)) :
    eventProbability (p.map f) event =
      eventProbability (p.map g) event' := by
  unfold eventProbability
  rw [PMF.map_comp, PMF.map_comp]
  have hfun : event ∘ f = event' ∘ g := by
    funext x
    exact propext (h x)
  rw [hfun]

/-- The probability of a union of two events is at most the sum. -/
theorem eventProbability_or_le (p : PMF γ) (event event' : γ → Prop) :
    eventProbability p (fun x => event x ∨ event' x) ≤
      eventProbability p event + eventProbability p event' := by
  rw [eventProbability_eq_toMeasure, eventProbability_eq_toMeasure,
    eventProbability_eq_toMeasure]
  have hset :
      {x | event x ∨ event' x} = {x | event x} ∪ {x | event' x} := by
    ext x
    simp
  rw [hset]
  exact measure_union_le _ _

/-- An impossible event has probability zero. -/
@[simp]
theorem eventProbability_false (p : PMF γ) :
    eventProbability p (fun _ => False) = 0 := by
  rw [eventProbability_eq_toMeasure]
  simp

/-- On a finite sample space, event probability is a finite weighted sum. -/
theorem eventProbability_eq_sum [Fintype γ] (p : PMF γ) (event : γ → Prop)
    [DecidablePred event] :
    eventProbability p event =
      ∑ x, if event x then p x else 0 := by
  classical
  rw [eventProbability_eq_toMeasure, PMF.toMeasure_apply_fintype]
  apply Finset.sum_congr rfl
  intro x _
  simp [Set.indicator]

/-- The real value of a finite event probability is its real weighted sum. -/
theorem eventProbability_toReal_eq_sum [Fintype γ]
    (p : PMF γ) (event : γ → Prop) [DecidablePred event] :
    (eventProbability p event).toReal =
      ∑ x, if event x then (p x).toReal else 0 := by
  rw [eventProbability_eq_sum, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x _
    split <;> simp_all
  · intro x _
    split
    · exact p.apply_ne_top x
    · simp

end EventsAndIntegrals

/-- Integration against a finite PMF is its finite weighted expectation. -/
theorem finitePMF_integral_eq_sum {γ : Type u} [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : PMF γ) (f : γ → E) :
    ∫ x, f x ∂p.toMeasure = ∑ x, (p x).toReal • f x :=
  PMF.integral_eq_sum p f

end CertifiedProjections
