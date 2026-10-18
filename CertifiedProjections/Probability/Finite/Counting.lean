/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Probability.Finite.UniformPiBridge
import CertifiedProjections.Model.Distributions.Signs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Set.PowersetCard

/-!
# Exact counting for finite uniform experiments

Reusable equivalences and cardinality formulas for Boolean functions, together
with the bridge from uniform finite counting to `eventProbability`.
-/

open scoped BigOperators ENNReal

namespace CertifiedProjections
namespace Probability

/-- The finite set of coordinates on which a Boolean function is true. -/
def boolSupport {α : Type*} [Fintype α]
    (f : α → Bool) : Finset α :=
  Finset.univ.filter fun i => f i = true

/-- Boolean functions correspond to their finite sets of true coordinates. -/
def boolFunEquivFinset (α : Type*) [Fintype α] [DecidableEq α] :
    (α → Bool) ≃ Finset α where
  toFun := boolSupport
  invFun s i := decide (i ∈ s)
  left_inv f := by
    funext i
    simp [boolSupport]
  right_inv s := by
    ext i
    simp [boolSupport]

/-- Fixed-cardinality finite sets as members of `powersetCard`. -/
def finsetCardSubtypeEquiv
    (α : Type*) [Fintype α] (k : ℕ) :
    {s : Finset α // s.card = k} ≃
      {s : Finset α // s ∈ Finset.univ.powersetCard k} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun s => by
    simp

theorem card_finset_card_subtype
    (α : Type*) [Fintype α] (k : ℕ) :
    Fintype.card {s : Finset α // s.card = k} =
      (Fintype.card α).choose k := by
  classical
  rw [Fintype.card_congr (finsetCardSubtypeEquiv α k)]
  rw [Fintype.card_coe]
  exact Finset.card_powersetCard k (Finset.univ : Finset α)

theorem card_bool_true_count
    (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card {f : α → Bool // (boolSupport f).card = k} =
      (Fintype.card α).choose k := by
  let e :
      {f : α → Bool // (boolSupport f).card = k} ≃
        {s : Finset α // s.card = k} :=
    Equiv.subtypeEquiv (boolFunEquivFinset α) fun _ => Iff.rfl
  exact (Fintype.card_congr e).trans
    (card_finset_card_subtype α k)

/-- View a pair of bits as a function on `Fin 2`. -/
def pairBit (b : Bool × Bool) : Fin 2 → Bool :=
  ![b.1, b.2]

/-- View a function on `Fin 2` as a pair of bits. -/
def bitPair (b : Fin 2 → Bool) : Bool × Bool :=
  (b 0, b 1)

@[simp]
theorem bitPair_pairBit (b : Bool × Bool) :
    bitPair (pairBit b) = b := by
  rcases b with ⟨b₀, b₁⟩
  rfl

@[simp]
theorem pairBit_bitPair (b : Fin 2 → Bool) :
    pairBit (bitPair b) = b := by
  funext i
  fin_cases i <;> rfl

/-- Sum of Rademacher signs in terms of the number of true bits. -/
theorem sum_signBit_eq_trueCount {n : ℕ} (f : Fin n → Bool) :
    ∑ i, signBit (f i) =
      2 * ((boolSupport f).card : ℤ) - n := by
  calc
    ∑ i, signBit (f i) =
        ∑ i, (2 * (if f i = true then (1 : ℤ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : f i <;> simp [signBit]
    _ = 2 * (∑ i, if f i = true then (1 : ℤ) else 0) - n := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
      simp
    _ = 2 * ((boolSupport f).card : ℤ) - n := by
      simp [boolSupport]

/-- Split a function into its restrictions to a predicate and its complement. -/
def piSplitEquiv {α β : Type*} (p : α → Prop) [DecidablePred p] :
    (α → β) ≃ ({i // p i} → β) × ({i // ¬ p i} → β) where
  toFun f := (fun i => f i, fun i => f i)
  invFun fg i := if hi : p i then fg.1 ⟨i, hi⟩ else fg.2 ⟨i, hi⟩
  left_inv f := by
    funext i
    simp
  right_inv fg := by
    apply Prod.ext
    · funext i
      simp [i.2]
    · funext i
      simp [i.2]

/-- Reassociate a product subtype whose predicate depends only on the left side. -/
def subtypeProdLeftEquiv {α β : Type*} (p : α → Prop) :
    {x : α × β // p x.1} ≃ {a : α // p a} × β where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2)
  invFun x := ⟨(x.1.1, x.2), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Count true values of a Boolean function on coordinates satisfying `p`. -/
def trueCountOn {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (f : α → Bool) : ℕ :=
  (Finset.univ.filter fun i => p i ∧ f i = true).card

theorem trueCountOn_eq_support_restrict
    {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (f : α → Bool) :
    trueCountOn p f =
      (boolSupport (fun i : {i // p i} => f i)).card := by
  classical
  unfold trueCountOn boolSupport
  apply Finset.card_bij
      (fun i hi => ⟨i, (Finset.mem_filter.mp hi).2.1⟩)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hi).2.2
  · intro a₁ ha₁ a₂ ha₂ h
    exact congr_arg Subtype.val h
  · intro b hb
    refine ⟨b.1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨b.2, (Finset.mem_filter.mp hb).2⟩
    · rfl

/-- Decompose a Boolean function with exactly `k` true selected coordinates. -/
def trueCountExactEquiv
    {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (t : ℕ) :
    {f : α → Bool // trueCountOn p f = t} ≃
      {f : {i // p i} → Bool // (boolSupport f).card = t} ×
        ({i // ¬ p i} → Bool) := by
  refine (Equiv.subtypeEquiv (piSplitEquiv p) fun f => ?_).trans
    (subtypeProdLeftEquiv
      (fun f : {i // p i} → Bool => (boolSupport f).card = t))
  rw [trueCountOn_eq_support_restrict]
  rfl

theorem card_trueCountOn_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (t : ℕ) :
    Fintype.card {f : α → Bool // trueCountOn p f = t} =
      (Fintype.card {i // p i}).choose t *
        2 ^ Fintype.card {i // ¬ p i} := by
  rw [Fintype.card_congr (trueCountExactEquiv p t),
    Fintype.card_prod, card_bool_true_count, Fintype.card_fun,
    Fintype.card_bool]

/-- Decompose a Boolean function with fewer than `k` true selected coordinates. -/
def trueCountLtEquiv
    {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (k : ℕ) :
    {f : α → Bool // trueCountOn p f < k} ≃
      (t : Fin k) × {f : α → Bool // trueCountOn p f = t} :=
  (Equiv.sigmaSubtypeFiberEquivSubtype
      (f := trueCountOn p)
      (p := fun f => trueCountOn p f < k)
      (q := fun t : ℕ => t < k)
      (fun _ => Iff.rfl)).symm |>.trans
    (Equiv.sigmaCongrLeft Fin.equivSubtype).symm

theorem card_trueCountOn_lt
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (k : ℕ) :
    Fintype.card {f : α → Bool // trueCountOn p f < k} =
      (∑ t ∈ Finset.range k,
          (Fintype.card {i // p i}).choose t) *
        2 ^ Fintype.card {i // ¬ p i} := by
  rw [Fintype.card_congr (trueCountLtEquiv p k),
    Fintype.card_sigma]
  simp_rw [card_trueCountOn_eq]
  rw [← Finset.sum_mul, Finset.sum_fin_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [dif_pos (Finset.mem_range.mp ht)]

theorem eventProbability_uniform_eq_card
    {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (event : α → Prop) [DecidablePred event] :
    eventProbability (PMF.uniformOfFintype α) event =
      Fintype.card {x : α // event x} *
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [eventProbability_eq_sum]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype event]

/-- Pairing a finite uniform event through an equivalence gives a reusable
`half plus bad` bound.  The hypothesis says that two paired outcomes cannot
both satisfy `event` unless the first outcome lies in `bad`. -/
theorem two_mul_eventProbability_uniform_toReal_le_one_add_bad
    {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (e : α ≃ α) (event bad : α → Prop)
    (hpair : ∀ x, event x → event (e x) → bad x) :
    2 * (eventProbability (PMF.uniformOfFintype α) event).toReal ≤
      1 + (eventProbability (PMF.uniformOfFintype α) bad).toReal := by
  classical
  let A : Finset α := Finset.univ.filter event
  let B : Finset α := Finset.univ.filter fun x => event (e x)
  let C : Finset α := Finset.univ.filter bad
  have hcardAB : A.card = B.card := by
    have hequiv : {x : α // event (e x)} ≃ {x : α // event x} :=
      Equiv.subtypeEquiv e (fun _ => Iff.rfl)
    calc
      A.card = Fintype.card {x : α // event x} :=
        (Fintype.card_subtype event).symm
      _ = Fintype.card {x : α // event (e x)} :=
        (Fintype.card_congr hequiv).symm
      _ = B.card := Fintype.card_subtype fun x => event (e x)
  have hinter : A ∩ B ⊆ C := by
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    have hxA : event x := by simpa [A] using hx'.1
    have hxB : event (e x) := by simpa [B] using hx'.2
    simpa [C] using hpair x hxA hxB
  have hcard : 2 * A.card ≤ Fintype.card α + C.card := by
    calc
      2 * A.card = A.card + B.card := by omega
      _ = (A ∪ B).card + (A ∩ B).card :=
        (Finset.card_union_add_card_inter A B).symm
      _ ≤ Fintype.card α + C.card :=
        Nat.add_le_add (by simpa using Finset.card_le_univ (A ∪ B))
          (Finset.card_le_card hinter)
  rw [eventProbability_uniform_eq_card,
    eventProbability_uniform_eq_card]
  have hα : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [Fintype.card_subtype, Fintype.card_subtype]
  change 2 * ((A.card : ℝ) * (Fintype.card α : ℝ)⁻¹) ≤
    1 + (C.card : ℝ) * (Fintype.card α : ℝ)⁻¹
  have hcardReal : 2 * (A.card : ℝ) ≤
      (Fintype.card α : ℝ) + C.card := by
    exact_mod_cast hcard
  calc
    2 * ((A.card : ℝ) * (Fintype.card α : ℝ)⁻¹) =
        (2 * (A.card : ℝ)) / Fintype.card α := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ ((Fintype.card α : ℝ) + C.card) / Fintype.card α :=
      (div_le_div_iff_of_pos_right hα).2 hcardReal
    _ = 1 + (C.card : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      field_simp [hα.ne']

theorem eventProbability_map_uniform_eq_card
    {α β : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → β) (event : β → Prop)
    [DecidablePred fun x => event (f x)] :
    eventProbability ((PMF.uniformOfFintype α).map f) event =
      Fintype.card {x : α // event (f x)} *
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [show eventProbability ((PMF.uniformOfFintype α).map f) event =
      eventProbability (PMF.uniformOfFintype α)
        (fun x => event (f x)) by
    unfold eventProbability
    rw [PMF.map_comp]
    rfl]
  exact eventProbability_uniform_eq_card _

/-- A point mass in the image of a finite uniform law is its fiber count. -/
theorem map_uniform_apply_eq_card
    {α β : Type*} [Fintype α] [Nonempty α]
    (f : α → β) (y : β) [DecidablePred fun x => f x = y] :
    ((PMF.uniformOfFintype α).map f) y =
      Fintype.card {x : α // f x = y} *
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
  let : DecidablePred (fun x : α => y = f x) :=
    fun x => decidable_of_iff (f x = y) eq_comm
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  rw [show
      (Finset.univ.filter fun x : α => y = f x) =
        Finset.univ.filter fun x : α => f x = y by
      ext x
      simp [eq_comm]]
  exact (Fintype.card_subtype fun x => f x = y).symm

/-- Projecting a finite uniform product onto its first factor stays uniform. -/
theorem map_uniformOfFintype_prod_fst
    (α β : Type*) [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst =
      PMF.uniformOfFintype α := by
  classical
  apply PMF.ext
  intro a
  rw [map_uniform_apply_eq_card]
  let e : {x : α × β // x.1 = a} ≃ β := {
    toFun x := x.1.2
    invFun b := ⟨(a, b), rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact Prod.ext x.2.symm rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]
  simp only [PMF.uniformOfFintype_apply]
  push_cast
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))]
  calc
    (Fintype.card β : ℝ≥0∞) *
          ((Fintype.card α : ℝ≥0∞)⁻¹ *
            (Fintype.card β : ℝ≥0∞)⁻¹) =
        (Fintype.card α : ℝ≥0∞)⁻¹ *
          ((Fintype.card β : ℝ≥0∞) *
            (Fintype.card β : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = (Fintype.card α : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv_cancel]
      · simp
      · exact_mod_cast Fintype.card_ne_zero
      · exact ENNReal.natCast_ne_top _

/-- Projecting a finite uniform product onto its second factor stays uniform. -/
theorem map_uniformOfFintype_prod_snd
    (α β : Type*) [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.snd =
      PMF.uniformOfFintype β := by
  calc
    (PMF.uniformOfFintype (α × β)).map Prod.snd =
        ((PMF.uniformOfFintype (α × β)).map (Equiv.prodComm α β)).map
          Prod.fst := by
            rw [PMF.map_comp]
            rfl
    _ = (PMF.uniformOfFintype (β × α)).map Prod.fst := by
      rw [map_uniformOfFintype_equiv]
    _ = PMF.uniformOfFintype β := map_uniformOfFintype_prod_fst β α

/-- A uniform finite product is generated by first sampling its first factor. -/
theorem uniformOfFintype_prod_eq_bind
    (α β : Type*) [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind fun a =>
        (PMF.uniformOfFintype β).map fun b => (a, b) := by
  classical
  apply PMF.ext
  intro x
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single x.1]
  · rw [Finset.sum_eq_single x.2]
    · simp only [Prod.eta, if_true]
      rw [Fintype.card_prod]
      push_cast
      rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _))]
    · intro b hb hne
      rw [if_neg]
      intro h
      exact hne (congrArg Prod.snd h).symm
    · simp
  · intro a ha hne
    have hfalse : ∀ b : β, x ≠ (a, b) := by
      intro b h
      exact hne (congrArg Prod.fst h).symm
    simp [hfalse]
  · simp

/-- A mapped finite uniform product averages its conditional event probabilities. -/
theorem eventProbability_map_uniform_prod_toReal
    {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    (f : α → β → γ) (event : γ → Prop) :
    (eventProbability
        ((PMF.uniformOfFintype (α × β)).map fun x => f x.1 x.2)
        event).toReal =
      ∑ a : α, (Fintype.card α : ℝ)⁻¹ *
        (eventProbability
          ((PMF.uniformOfFintype β).map (f a)) event).toReal := by
  classical
  let : MeasurableSpace (α × β) := ⊤
  let : MeasurableSpace β := ⊤
  rw [show eventProbability
      ((PMF.uniformOfFintype (α × β)).map fun x => f x.1 x.2) event =
        eventProbability (PMF.uniformOfFintype (α × β))
          (fun x => event (f x.1 x.2)) by
    unfold eventProbability
    rw [PMF.map_comp]
    rfl]
  rw [eventProbability_toReal_eq_sum]
  simp_rw [show ∀ a, eventProbability
      ((PMF.uniformOfFintype β).map (f a)) event =
        eventProbability (PMF.uniformOfFintype β)
          (fun b => event (f a b)) by
    intro a
    unfold eventProbability
    rw [PMF.map_comp]
    rfl]
  simp_rw [eventProbability_toReal_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_prod, Nat.cast_mul]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp_all
  field_simp

end Probability
end CertifiedProjections
