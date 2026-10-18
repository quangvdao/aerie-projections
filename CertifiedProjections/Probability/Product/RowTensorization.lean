/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Distributions.Entry

/-!
# Exact tensorization of finite row events

This module turns independence of finitely many random coordinates into an
exact product formula for conjunctions of coordinate events.  Its principal
specialization says that an event holds in every row of a sparse-Rademacher
matrix with probability equal to the corresponding one-row probability raised
to the number of rows.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

universe u v w

/--
The probability of a finite union of discrete events is at most the sum of
their probabilities.  This is the finite-union bridge used after partitioning
a row event into coordinate-indexed bad events.
-/
theorem eventProbability_exists_le_sum
    {ι : Type u} [Fintype ι]
    {α : Type v} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p : PMF α) (event : ι → α → Prop) :
    eventProbability p (fun x => ∃ i, event i x) ≤
      ∑ i, eventProbability p (event i) := by
  rw [eventProbability_eq_toMeasure]
  have hset : {x | ∃ i, event i x} = ⋃ i, {x | event i x} := by
    ext x
    simp
  rw [hset]
  simpa only [eventProbability_eq_toMeasure] using
    measure_iUnion_fintype_le p.toMeasure (fun i => {x | event i x})

/--
If every coordinate satisfies either its main event or its exceptional event,
then either every main event holds or some exceptional event holds.
-/
theorem eventProbability_forall_or_le
    {ι : Type u} [Fintype ι]
    {α : Type v} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p : PMF α) (main exceptional : ι → α → Prop) :
    eventProbability p (fun x => ∀ i, main i x ∨ exceptional i x) ≤
      eventProbability p (fun x => ∀ i, main i x) +
        ∑ i, eventProbability p (exceptional i) := by
  calc
    eventProbability p (fun x => ∀ i, main i x ∨ exceptional i x) ≤
        eventProbability p
          (fun x => (∀ i, main i x) ∨ ∃ i, exceptional i x) := by
      apply eventProbability_mono
      intro x hx
      by_cases hmain : ∀ i, main i x
      · exact Or.inl hmain
      · right
        push Not at hmain
        obtain ⟨i, hi⟩ := hmain
        exact ⟨i, (hx i).resolve_left hi⟩
    _ ≤ eventProbability p (fun x => ∀ i, main i x) +
          eventProbability p (fun x => ∃ i, exceptional i x) :=
      eventProbability_or_le p _ _
    _ ≤ eventProbability p (fun x => ∀ i, main i x) +
          ∑ i, eventProbability p (exceptional i) :=
      by
        simpa [add_comm] using
          add_le_add_left (eventProbability_exists_le_sum p exceptional)
            (eventProbability p (fun x => ∀ i, main i x))

/-- In a discrete probability experiment, the probability of the complement
of an event is one minus the probability of the event. -/
theorem eventProbability_compl_eq_one_sub
    {α : Type u} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p : PMF α) (event : α → Prop) :
    eventProbability p (fun x => ¬ event x) =
      1 - eventProbability p event := by
  rw [eventProbability_eq_toMeasure, eventProbability_eq_toMeasure]
  have hset : {x | ¬ event x} = {x | event x}ᶜ := by rfl
  rw [hset, measure_compl
    (Set.Countable.measurableSet (Set.to_countable _)) (measure_ne_top _ _)]
  simp

/--
The probability that every member of a finite independent family satisfies
its own event is the product of the marginal event probabilities.

The discrete hypotheses make every function and event measurable.  This is
the natural boundary for the finite PMF experiments used by CertifiedProjections.
-/
theorem eventProbability_iIndepFun_forall_eq_prod
    {ι : Type u} [Fintype ι]
    {Ω : Type v} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    {κ : ι → Type w} [∀ i, Countable (κ i)]
    [∀ i, MeasurableSpace (κ i)] [∀ i, MeasurableSingletonClass (κ i)]
    (p : PMF Ω) (f : (i : ι) → Ω → κ i)
    (event : (i : ι) → κ i → Prop)
    (hindep : iIndepFun f p.toMeasure) :
    eventProbability p (fun ω => ∀ i, event i (f i ω)) =
      ∏ i, eventProbability (p.map (f i)) (event i) := by
  rw [eventProbability_eq_toMeasure]
  have hset :
      {ω | ∀ i, event i (f i ω)} =
        ⋂ i, {ω | event i (f i ω)} := by
    ext ω
    simp
  rw [hset, hindep.meas_iInter]
  · apply Finset.prod_congr rfl
    intro i _
    rw [eventProbability_eq_toMeasure]
    exact (PMF.toMeasure_map_apply
      (p := p) (f := f i) (s := {x | event i x})
      (measurable_of_countable (f i))
      (Set.Countable.measurableSet (Set.to_countable _))).symm
  · intro i
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨{x | event i x},
      Set.Countable.measurableSet (Set.to_countable _), rfl⟩

/-- The probability that some member of a finite independent family satisfies
its event is one minus the product of the complementary marginal
probabilities. -/
theorem eventProbability_iIndepFun_exists_eq_one_sub_prod
    {ι : Type u} [Fintype ι]
    {Ω : Type v} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    {κ : ι → Type w} [∀ i, Countable (κ i)]
    [∀ i, MeasurableSpace (κ i)] [∀ i, MeasurableSingletonClass (κ i)]
    (p : PMF Ω) (f : (i : ι) → Ω → κ i)
    (event : (i : ι) → κ i → Prop)
    (hindep : iIndepFun f p.toMeasure) :
    eventProbability p (fun ω => ∃ i, event i (f i ω)) =
      1 - ∏ i, (1 - eventProbability (p.map (f i)) (event i)) := by
  calc
    eventProbability p (fun ω => ∃ i, event i (f i ω)) =
        eventProbability p (fun ω => ¬ ∀ i, ¬ event i (f i ω)) := by
      apply eventProbability_congr
      intro ω
      simp
    _ = 1 - eventProbability p (fun ω => ∀ i, ¬ event i (f i ω)) :=
      eventProbability_compl_eq_one_sub _ _
    _ = 1 - ∏ i, eventProbability (p.map (f i)) (fun x => ¬ event i x) := by
      rw [eventProbability_iIndepFun_forall_eq_prod p f
        (fun i x => ¬ event i x) hindep]
    _ = 1 - ∏ i, (1 - eventProbability (p.map (f i)) (event i)) := by
      simp_rw [eventProbability_compl_eq_one_sub]

/-- Different fixed row events factor into their marginal probabilities. -/
theorem sparseRademacherMatrix_eventProbability_allRows_eq_prod
    (m d : ℕ) (event : Fin m → (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∀ j, event j (J j)) =
      ∏ j, eventProbability (sparseRademacherRow d) (event j) := by
  rw [eventProbability_iIndepFun_forall_eq_prod
    (p := sparseRademacherMatrix m d)
    (f := fun j J => J j) (event := event)
    (sparseRademacherMatrix_iIndepRows m d)]
  simp_rw [sparseRademacherMatrix_rowMarginal]

/-- Exact complement-product formula for row-dependent events of a
sparse-Rademacher matrix, including unequal fixed affine shifts. -/
theorem sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_prod
    (m d : ℕ) (event : Fin m → (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∃ j, event j (J j)) =
      1 - ∏ j, (1 - eventProbability (sparseRademacherRow d) (event j)) := by
  rw [eventProbability_iIndepFun_exists_eq_one_sub_prod
    (p := sparseRademacherMatrix m d)
    (f := fun j J => J j) (event := event)
    (sparseRademacherMatrix_iIndepRows m d)]
  simp_rw [sparseRademacherMatrix_rowMarginal]

/-- A uniform marginal bound applies to different fixed events in different
rows, in particular to row-dependent affine shifts. -/
theorem sparseRademacherMatrix_eventProbability_varyingRows_le_pow
    (m d : ℕ) (event : Fin m → (Fin d → ℤ) → Prop) (c : ℝ≥0∞)
    (hrow : ∀ j, eventProbability (sparseRademacherRow d) (event j) ≤ c) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∀ j, event j (J j)) ≤ c ^ m := by
  rw [sparseRademacherMatrix_eventProbability_allRows_eq_prod]
  calc
    ∏ j, eventProbability (sparseRademacherRow d) (event j) ≤
        ∏ _j : Fin m, c := Finset.prod_le_prod' (fun j _ => hrow j)
    _ = c ^ m := Fin.prod_const m c

/-- Real-valued version of varying-row tensorization. -/
theorem sparseRademacherMatrix_eventProbability_varyingRows_toReal_le_pow
    (m d : ℕ) (event : Fin m → (Fin d → ℤ) → Prop) (c : ℝ)
    (_hc : 0 ≤ c)
    (hrow : ∀ j, (eventProbability (sparseRademacherRow d) (event j)).toReal ≤ c) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => ∀ j, event j (J j))).toReal ≤ c ^ m := by
  rw [sparseRademacherMatrix_eventProbability_allRows_eq_prod,
    ENNReal.toReal_prod]
  calc
    ∏ j, (eventProbability (sparseRademacherRow d) (event j)).toReal ≤
        ∏ _j : Fin m, c :=
      Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun j _ => hrow j)
    _ = c ^ m := Fin.prod_const m c

/--
An event holds in every row of an `m × d` sparse-Rademacher matrix with
probability equal to its one-row probability raised to `m`.
-/
theorem sparseRademacherMatrix_eventProbability_allRows_eq_pow
    (m d : ℕ) (event : (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∀ j, event (J j)) =
      eventProbability (sparseRademacherRow d) event ^ m := by
  rw [eventProbability_iIndepFun_forall_eq_prod
    (p := sparseRademacherMatrix m d)
    (f := fun j J => J j) (event := fun _ => event)
    (sparseRademacherMatrix_iIndepRows m d)]
  simp_rw [sparseRademacherMatrix_rowMarginal]
  exact Fin.prod_const m
    (eventProbability (sparseRademacherRow d) event)

/-- Exact `1 - (1 - r)^m` formula for an identical event in every independent
sparse-Rademacher row. -/
theorem sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_pow
    (m d : ℕ) (event : (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∃ j, event (J j)) =
      1 - (1 - eventProbability (sparseRademacherRow d) event) ^ m := by
  rw [sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_prod]
  exact congrArg (fun x => 1 - x) (Fin.prod_const m _)

/-- A uniform one-row upper bound tensorizes across all sparse matrix rows. -/
theorem sparseRademacherMatrix_eventProbability_allRows_le_pow
    (m d : ℕ) (event : (Fin d → ℤ) → Prop) (c : ℝ≥0∞)
    (hrow : eventProbability (sparseRademacherRow d) event ≤ c) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∀ j, event (J j)) ≤ c ^ m := by
  rw [sparseRademacherMatrix_eventProbability_allRows_eq_pow]
  exact pow_le_pow_left' hrow m

/--
Tensorize the main row event and pay a finite union bound for exceptional
rows.  This is the exact composition used in the small-norm SparseLInf regime.
-/
theorem sparseRademacherMatrix_eventProbability_allRows_or_le_pow_add
    (m d : ℕ) (main exceptional : (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∀ j, main (J j) ∨ exceptional (J j)) ≤
      eventProbability (sparseRademacherRow d) main ^ m +
        m • eventProbability (sparseRademacherRow d) exceptional := by
  calc
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∀ j, main (J j) ∨ exceptional (J j)) ≤
      eventProbability (sparseRademacherMatrix m d)
          (fun J => ∀ j, main (J j)) +
        ∑ j : Fin m, eventProbability (sparseRademacherMatrix m d)
          (fun J => exceptional (J j)) :=
      eventProbability_forall_or_le
        (p := sparseRademacherMatrix m d)
        (main := fun j (J : Matrix (Fin m) (Fin d) ℤ) => main (J j))
        (exceptional := fun j (J : Matrix (Fin m) (Fin d) ℤ) => exceptional (J j))
    _ = eventProbability (sparseRademacherRow d) main ^ m +
        m • eventProbability (sparseRademacherRow d) exceptional := by
      rw [sparseRademacherMatrix_eventProbability_allRows_eq_pow]
      congr 1
      simp_rw [show ∀ j : Fin m,
          eventProbability (sparseRademacherMatrix m d)
              (fun J => exceptional (J j)) =
            eventProbability (sparseRademacherRow d) exceptional by
        intro j
        calc
          eventProbability (sparseRademacherMatrix m d)
              (fun J => exceptional (J j)) =
            eventProbability
              ((sparseRademacherMatrix m d).map (fun J => J j))
              exceptional := by
                unfold eventProbability
                rw [PMF.map_comp]
                simp [Function.comp_def]
          _ = eventProbability (sparseRademacherRow d) exceptional := by
            rw [sparseRademacherMatrix_rowMarginal]]
      simp

end CertifiedProjections
