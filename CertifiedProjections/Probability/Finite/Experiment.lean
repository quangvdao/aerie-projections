/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite probability experiments

This module contains the distribution-independent primitives used to build
finite product experiments and measure events under a probability mass
function.
-/

namespace CertifiedProjections

universe u v w

open MeasureTheory

/-- The uniform PMF on finite dependent functions `x : (i : ι) → α i`.
Equivalently, every coordinate `x i` is sampled independently and uniformly
from `α i`. -/
noncomputable def uniformPiPMF {ι : Type u} [Fintype ι]
    (α : ι → Type v) [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] :
    PMF ((i : ι) → α i) :=
  @PMF.uniformOfFintype ((i : ι) → α i)
    (Fintype.ofFinite ((i : ι) → α i)) inferInstance

/-- Apply a coordinatewise map to a uniform finite function. The source
coordinates are independent, so their images are independent as well. -/
noncomputable def uniformPiMap {ι : Type u} [Fintype ι]
    {α : ι → Type v} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    {β : ι → Type w} (f : (i : ι) → α i → β i) :
    PMF ((i : ι) → β i) :=
  (uniformPiPMF α).map fun x i => f i (x i)

/-- Probability of a proposition under a PMF, represented as an extended
nonnegative real. -/
noncomputable def eventProbability {α : Type*} (p : PMF α) (event : α → Prop) :
    ENNReal :=
  (p.map event) True

/-- Pointwise equivalent predicates have the same probability under a PMF. -/
theorem eventProbability_congr {α : Type*} (p : PMF α)
    {event event' : α → Prop} (h : ∀ x, event x ↔ event' x) :
    eventProbability p event = eventProbability p event' := by
  congr 1
  funext x
  exact propext (h x)

/-- For a countable discrete sample space, `eventProbability` is the measure
of the set on which the event holds. -/
theorem eventProbability_eq_toMeasure
    {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p : PMF α) (event : α → Prop) :
    eventProbability p event = p.toMeasure {x | event x} := by
  have hevent : Measurable event := fun _ _ =>
    Set.Countable.measurableSet (Set.to_countable _)
  rw [eventProbability]
  rw [← PMF.toMeasure_apply_singleton (p.map event) True
    (measurableSet_singleton True)]
  rw [PMF.toMeasure_map_apply event p {True} hevent
    (measurableSet_singleton True)]
  congr 1
  ext x
  simp

/-- Event probability is monotone under pointwise implication. -/
theorem eventProbability_mono
    {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p : PMF α) {event event' : α → Prop}
    (h : ∀ x, event x → event' x) :
    eventProbability p event ≤ eventProbability p event' := by
  rw [eventProbability_eq_toMeasure, eventProbability_eq_toMeasure]
  apply measure_mono
  intro x hx
  exact h x hx

end CertifiedProjections
