/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Expectation
import CertifiedProjections.Model.Distributions.SparseRademacher
import CertifiedProjections.Model.Distributions.Entry
import CertifiedProjections.Probability.Finite.Counting
import CertifiedProjections.Probability.Product.RowTensorization
import Mathlib.Logic.Equiv.Prod
import CertifiedProjections.Model.Vectors.Real
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.NNRat.Lemmas

/-!
# Entry laws

An `EntryLaw` is the law of one matrix entry, given as a uniform finite seed mapped to an integer.
This file defines the entry, row and matrix laws built from it (`entryPMF`, `rowPMF`, `matrixPMF`),
the entry laws `ternary` and `uniform b`, and the properties of an entry law used by the one-stage
lemmas: `Symmetric`, `NoTwoConsecutiveBound`, `AtomBound`, `MomentDominated` and `MGFConstant` (spec
H1, Lemma A, Lemma C, Lemmas 5.1 and 5.2). It proves the first four properties for `ternary` and
`uniform b`.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

/-- The law of one matrix entry: a uniform finite seed mapped to an integer. -/
structure EntryLaw where
  /-- The type of seeds. One entry is drawn by choosing a seed uniformly. -/
  Seed : Type
  /-- There are finitely many seeds. -/
  [fintype : Fintype Seed]
  /-- There is at least one seed. -/
  [nonempty : Nonempty Seed]
  /-- The integer value of the entry for each seed. -/
  value : Seed → ℤ
  /-- A bound on the absolute value of every entry. -/
  bound : ℕ
  /-- Every value has absolute value at most `bound`. -/
  natAbs_value_le : ∀ s, (value s).natAbs ≤ bound

attribute [instance] EntryLaw.fintype EntryLaw.nonempty

namespace EntryLaw
/-- The ternary entry law: the values −1, 0, 1 with masses 1/4, 1/2, 1/4. The seed type is
`Bool × Bool`, with `value := sparseBit` and `bound := 1`. -/
def ternary : EntryLaw where
  Seed := Bool × Bool
  value := sparseBit
  bound := 1
  natAbs_value_le := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> decide
/-- The uniform entry law on the integers from `-b` to `b`. The seed type is `Fin (2 * b + 1)`, with
`value s := (s : ℤ) - b` and `bound := b`. -/
def uniform (b : ℕ) : EntryLaw where
  Seed := Fin (2 * b + 1)
  value s := (s : ℤ) - b
  bound := b
  natAbs_value_le := by
    intro s
    have hs := s.isLt
    omega

/-- The law of one entry: the value `μ.value s` of a uniformly drawn seed `s`. -/
noncomputable def entryPMF (μ : EntryLaw) : PMF ℤ := (PMF.uniformOfFintype μ.Seed).map μ.value
/-- The law of a row of `f` independent entries, each drawn from `μ.entryPMF`. -/
noncomputable def rowPMF (μ : EntryLaw) (f : ℕ) : PMF (Fin f → ℤ) :=
  uniformPiMap (fun _ : Fin f => μ.value)
/-- The law of a matrix with `c` rows and `f` columns whose entries are independent draws from
`μ.entryPMF`. -/
noncomputable def matrixPMF (μ : EntryLaw) (c f : ℕ) : PMF (Fin c → Fin f → ℤ) :=
  uniformPiMap (fun _ : Fin c => fun (s : Fin f → μ.Seed) (i : Fin f) => μ.value (s i))
/-- If, for every choice of the other entries, an event on a row has probability at most `α` over
the entry in position `k`, then it has probability at most `α` over the whole row. -/
theorem eventProbability_rowPMF_le {f : ℕ} (μ : EntryLaw) (k : Fin f)
    (E : (Fin f → ℤ) → Prop) (α : ℝ≥0∞)
    (hentry : ∀ other, eventProbability μ.entryPMF
      (fun z => E (Function.update other k z)) ≤ α) :
    eventProbability (μ.rowPMF f) E ≤ α := by
  classical
  let e := (Equiv.funSplitAt k μ.Seed).trans (Equiv.prodComm _ _)
  let base (t : {j : Fin f // j ≠ k} → μ.Seed) : Fin f → ℤ :=
    fun j => μ.value (e.symm (t, Classical.choice μ.nonempty) j)
  have hrow (t : {j : Fin f // j ≠ k} → μ.Seed) (s : μ.Seed) :
      (fun j => μ.value (e.symm (t, s) j)) = Function.update (base t) k (μ.value s) := by
    funext j
    by_cases hj : j = k
    · subst j
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, base, hj]
  rw [EntryLaw.rowPMF, uniformPiMap, uniformPiPMF_eq_uniformOfFintype,
    ← map_uniformOfFintype_equiv e.symm, PMF.map_comp,
    Probability.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  unfold eventProbability
  rw [PMF.map_bind, PMF.bind_apply]
  calc
    _ ≤ ∑' t, PMF.uniformOfFintype _ t * α := by
      apply ENNReal.tsum_le_tsum
      intro t
      apply mul_le_mul_of_nonneg_left _ bot_le
      have ht := hentry (base t)
      unfold eventProbability EntryLaw.entryPMF at ht
      simpa only [PMF.map_comp, Function.comp_def, hrow] using ht
    _ = α := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- If the event `E` has probability at most `ρ` for one row, then `E` holds for all `c` rows of the
matrix with probability at most `ρ ^ c`. -/
theorem eventProbability_matrixPMF_forall_le (μ : EntryLaw) (c f : ℕ)
    (E : (Fin f → ℤ) → Prop) (ρ : ℝ≥0∞)
    (hrow : eventProbability (μ.rowPMF f) E ≤ ρ) :
    eventProbability (μ.matrixPMF c f) (fun C => ∀ j, E (C j)) ≤ ρ ^ c := by
  classical
  let : MeasurableSpace μ.Seed := ⊤
  have hindep := uniformPiMap_iIndep
    (fun _ : Fin c => fun (s : Fin f → μ.Seed) (i : Fin f) => μ.value (s i))
    (fun _ => measurable_of_finite _)
  rw [eventProbability_iIndepFun_forall_eq_prod
    (μ.matrixPMF c f) (fun j C => C j) (fun _ => E) hindep]
  have hmarg (j : Fin c) : (μ.matrixPMF c f).map (fun C => C j) = μ.rowPMF f := by
    rw [EntryLaw.matrixPMF, uniformPiMap_marginal]
    simp only [EntryLaw.rowPMF, uniformPiMap, uniformPiPMF_eq_uniformOfFintype]
  simp_rw [hmarg]
  calc
    _ ≤ ∏ _j : Fin c, ρ := Finset.prod_le_prod' (fun _ _ => hrow)
    _ = _ := Fin.prod_const c ρ
end EntryLaw

namespace EntryLaw
/-- The entry law is symmetric: `z` and `-z` have the same mass under `μ.entryPMF`. -/
def Symmetric (μ : EntryLaw) : Prop := ∀ z, μ.entryPMF (-z) = μ.entryPMF z
/-- Every set `P` of integers that contains no two consecutive integers has probability at most `ρ`
under `μ.entryPMF`. -/
def NoTwoConsecutiveBound (μ : EntryLaw) (ρ : ℝ≥0∞) : Prop :=
  ∀ P : Set ℤ, (∀ s, s ∈ P → s + 1 ∉ P) → eventProbability μ.entryPMF (· ∈ P) ≤ ρ
/-- Every integer `z` has mass at most `α` under `μ.entryPMF`. -/
def AtomBound (μ : EntryLaw) (α : ℝ≥0∞) : Prop := ∀ z, μ.entryPMF z ≤ α
/-- For every `d`, the moment of order `2 * d` of `μ.entryPMF` is at most the double factorial of
`2 * d - 1` times `s2 ^ d`, which is the moment of that order of a centered Gaussian of variance
`s2` (spec Lemma 5.1, hypothesis). -/
def MomentDominated (μ : EntryLaw) (s2 : ℝ≥0) : Prop :=
  ∀ d : ℕ, expectation μ.entryPMF (fun z => (z.natAbs : ℝ≥0∞) ^ (2 * d)) ≤
    (Nat.doubleFactorial (2 * d - 1) : ℝ≥0∞) * (s2 : ℝ≥0∞) ^ d
/-- For every row length `f` and every real vector `u` with `∑ i, u i ^ 2 = 1`, the expectation of
`exp (-t * realRowDot a u ^ 2)` over a row `a` drawn from `μ.rowPMF f` is at most `K` (spec Lemma C
with one column). -/
def MGFConstant (μ : EntryLaw) (t K : ℝ) : Prop :=
  ∀ (f : ℕ) (u : Fin f → ℝ), ∑ i, u i ^ 2 = 1 →
    expectation (μ.rowPMF f) (fun a => ENNReal.ofReal (Real.exp (-t * realRowDot a u ^ 2))) ≤
      ENNReal.ofReal K
end EntryLaw

namespace EntryLaw
/-- The expectation of `g` under `μ.entryPMF` is the average of `g (μ.value s)` over all seeds
`s`. -/
private theorem expectation_seed (μ : EntryLaw) (g : ℤ → ℝ≥0∞) :
    expectation μ.entryPMF g = (Fintype.card μ.Seed : ℝ≥0∞)⁻¹ * ∑ s, g (μ.value s) := by
  classical
  unfold expectation entryPMF
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [ite_mul, zero_mul, tsum_ite_eq, PMF.uniformOfFintype_apply]
  rw [tsum_fintype, ← Finset.mul_sum]

/-- The mass of `z` under `(uniform b).entryPMF` is `1 / (2 * b + 1)` if `-b ≤ z ≤ b`, and zero
otherwise. -/
private theorem uniform_apply (b : ℕ) (z : ℤ) :
    (uniform b).entryPMF z =
      if -(b : ℤ) ≤ z ∧ z ≤ b then (2 * b + 1 : ℝ≥0∞)⁻¹ else 0 := by
  classical
  change ((PMF.uniformOfFintype (Fin (2 * b + 1))).map
    (fun s : Fin (2 * b + 1) => (s : ℤ) - b)) z = _
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  split_ifs with hz
  · let s : Fin (2 * b + 1) := ⟨(z + b).toNat, by omega⟩
    have hs : z = (s : ℤ) - b := by dsimp [s]; omega
    rw [tsum_eq_single s]
    · simp [hs]
    · intro t ht
      have hne : z ≠ (t : ℤ) - b := by
        intro he
        apply ht
        apply Fin.ext
        have := t.isLt
        dsimp [s] at hs ⊢
        omega
      simp [hne]
  · have hne (s : Fin (2 * b + 1)) : z ≠ (s : ℤ) - b := by
      have := s.isLt
      omega
    simp [hne]

/-- In `ℝ≥0∞`, a quarter plus a quarter is a half. -/
private theorem quarter_add_quarter : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ = 2⁻¹ := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← add_mul,
    ENNReal.inv_two_add_inv_two, one_mul]

/-- `2 ^ d` is at most the double factorial of `2 * d + 1`. -/
private theorem two_pow_le_doubleFactorial (d : ℕ) :
    2 ^ d ≤ Nat.doubleFactorial (2 * d + 1) := by
  induction d with
  | zero => decide
  | succ d ih =>
    have he : 2 * (d + 1) + 1 = (2 * d + 1) + 2 := by omega
    rw [he, Nat.doubleFactorial_add_two, pow_succ]
    calc
      2 ^ d * 2 ≤ Nat.doubleFactorial (2 * d + 1) * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ (2 * d + 1 + 2) * Nat.doubleFactorial (2 * d + 1) := by
        rw [mul_comm]
        exact Nat.mul_le_mul_right _ (by omega)

/-- `1 / 2` is at most the double factorial of `2 * (d + 1) - 1` times `(1 / 2) ^ (d + 1)`. The left
side is the moment of order `2 * (d + 1)` of the ternary entry law, and the right side is that of a
centered Gaussian of variance `1 / 2`. -/
private theorem ternary_gaussian_bound (d : ℕ) : (1 / 2 : ℝ≥0∞) ≤
    Nat.doubleFactorial (2 * (d + 1) - 1) * (1 / 2 : ℝ≥0∞) ^ (d + 1) := by
  have h : (2 : ℝ≥0∞) ^ d ≤ Nat.doubleFactorial (2 * d + 1) := by
    exact_mod_cast two_pow_le_doubleFactorial d
  have ht : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
  rw [ht, pow_succ]
  calc
    (1 / 2 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ d * (1 / 2 : ℝ≥0∞) ^ d * (1 / 2) := by
      rw [← mul_pow, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      simp
    _ ≤ Nat.doubleFactorial (2 * d + 1) * (1 / 2 : ℝ≥0∞) ^ d * (1 / 2) := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact mul_le_mul_of_nonneg_right h zero_le
    _ = _ := by rw [mul_assoc]

/-- A closed form for the sum of `(i - b) ^ 2` over `i < n`. -/
private lemma sum_centered_sq (n b : ℕ) :
    (∑ i ∈ Finset.range n, ((i : ℝ) - b) ^ 2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 -
      (b : ℝ) * (n : ℝ) * ((n : ℝ) - 1) + (n : ℝ) * (b : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The sum over all seeds of the squared value of `uniform b` is
`(2 * b + 1) * b * (b + 1) / 3`. -/
private lemma sum_uniform_sq (b : ℕ) :
    (∑ s : Fin (2 * b + 1), (((s : ℤ) - b).natAbs : ℝ≥0∞) ^ 2) =
      ENNReal.ofReal (((2 * b + 1 : ℕ) : ℝ) * (b : ℝ) * ((b : ℝ) + 1) / 3) := by
  have hsq (s : Fin (2 * b + 1)) :
      ((((s : ℤ) - b).natAbs : ℝ≥0∞) ^ 2) =
        ENNReal.ofReal ((((s : ℕ) : ℝ) - (b : ℝ)) ^ 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]
    congr 1
    simp
  simp_rw [hsq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
    Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) - b) ^ 2), sum_centered_sq]
  congr 1
  push_cast
  ring

/-- The second moment of `(uniform b).entryPMF` is `b * (b + 1) / 3`. -/
private lemma uniform_second_moment (b : ℕ) :
    expectation (uniform b).entryPMF (fun z => (z.natAbs : ℝ≥0∞) ^ 2) =
      (((b * (b + 1) : ℕ) : ℝ≥0) / 3 : ℝ≥0) := by
  rw [expectation_seed]
  have hc : Fintype.card (uniform b).Seed = 2 * b + 1 := Fintype.card_fin _
  rw [hc]
  simp only [uniform]
  change ((2 * b + 1 : ℕ) : ℝ≥0∞)⁻¹ *
    (∑ s : Fin (2 * b + 1), (((s : ℤ) - b).natAbs : ℝ≥0∞) ^ 2) = _
  rw [sum_uniform_sq]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [ENNReal.div_eq_inv_mul]
  have he : (3 : ℝ≥0∞)⁻¹ * (↑(2 * b + 1 : ℕ) * ↑b * (↑b + 1)) =
      ↑(2 * b + 1 : ℕ) * ((↑b * (↑b + 1)) / 3) := by
    rw [ENNReal.div_eq_inv_mul]
    ac_rfl
  rw [he, ← mul_assoc,
    ENNReal.inv_mul_cancel (by positivity) (ENNReal.natCast_ne_top (2 * b + 1)), one_mul]
  simp only [ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_natCast,
    ENNReal.coe_ofNat, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- The moment of order `2 * (d + 1)` of `μ.entryPMF` is at most `μ.bound ^ (2 * d)` times its
second moment. -/
private lemma bounded_seed_moment (μ : EntryLaw) (d : ℕ) :
    expectation μ.entryPMF (fun z => (z.natAbs : ℝ≥0∞) ^ (2 * (d + 1))) ≤
      (μ.bound : ℝ≥0∞) ^ (2 * d) *
        expectation μ.entryPMF (fun z => (z.natAbs : ℝ≥0∞) ^ 2) := by
  rw [expectation_seed, expectation_seed]
  calc
    _ ≤ (Fintype.card μ.Seed : ℝ≥0∞)⁻¹ *
        ∑ s, (μ.bound : ℝ≥0∞) ^ (2 * d) * ((μ.value s).natAbs : ℝ≥0∞) ^ 2 := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro s _
      rw [Nat.mul_add, Nat.mul_one, pow_add]
      apply mul_le_mul_left
      exact pow_le_pow_left' (by exact_mod_cast μ.natAbs_value_le s) _
    _ = _ := by rw [← Finset.mul_sum]; ac_rfl

/-- `3 ^ d` is at most the double factorial of `2 * d + 1`. -/
private lemma doubleFactorial_ge_three_pow (d : ℕ) :
    3 ^ d ≤ Nat.doubleFactorial (2 * d + 1) := by
  induction d with
  | zero => decide
  | succ d ih =>
    have he : 2 * (d + 1) + 1 = (2 * d + 1) + 2 := by omega
    rw [he, Nat.doubleFactorial_add_two, pow_succ]
    exact (Nat.mul_le_mul_right 3 ih).trans (by
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_left (Nat.doubleFactorial (2 * d + 1))
          (show 3 ≤ 2 * d + 1 + 2 by omega))

/-- The ternary entry law is symmetric. -/
theorem ternary_symmetric : ternary.Symmetric := by
  intro z
  change sparseEntryPMF (-z) = sparseEntryPMF z
  by_cases hn : z = -1
  · subst z; simp
  by_cases hz : z = 0
  · subst z; simp
  by_cases hp : z = 1
  · subst z; simp
  rw [sparseEntryPMF_eq_zero hn hz hp,
    sparseEntryPMF_eq_zero (by omega) (by omega) (by omega)]
/-- Under the ternary entry law, every set of integers with no two consecutive elements has
probability at most `1 / 2`. -/
theorem ternary_noTwoConsecutiveBound : ternary.NoTwoConsecutiveBound (1 / 2) := by
  classical
  intro P hP
  have hneg : (0 : ℤ) ∈ P → (-1 : ℤ) ∉ P := by
    intro hz hn
    exact hP (-1) hn (by simpa using hz)
  have hpos : (0 : ℤ) ∈ P → (1 : ℤ) ∉ P := by
    intro hz
    exact hP 0 hz
  change eventProbability ((PMF.uniformOfFintype (Bool × Bool)).map sparseBit) (· ∈ P) ≤ _
  unfold eventProbability
  rw [PMF.map_comp, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_bool,
    Fintype.sum_prod_type, Fintype.sum_bool, Function.comp_apply]
  by_cases hz : (0 : ℤ) ∈ P
  · simp [sparseBit, hz, hneg hz, hpos hz, quarter_add_quarter]
  · by_cases hn : (-1 : ℤ) ∈ P <;> by_cases hp : (1 : ℤ) ∈ P <;>
      simp [sparseBit, hz, hn, hp, quarter_add_quarter] <;> norm_num
/-- Under the ternary entry law, every integer has mass at most `1 / 2`. -/
theorem ternary_atomBound : ternary.AtomBound (1 / 2) := by
  intro z
  change sparseEntryPMF z ≤ 1 / 2
  by_cases hn : z = -1
  · subst z; simp; norm_num
  by_cases hz : z = 0
  · subst z; simp
  by_cases hp : z = 1
  · subst z; simp; norm_num
  rw [sparseEntryPMF_eq_zero hn hz hp]
  exact bot_le
/-- The even moments of the ternary entry law are at most those of a centered Gaussian of variance
`1 / 2`. -/
theorem ternary_momentDominated : ternary.MomentDominated (1 / 2) := by
  intro d
  rw [expectation_seed]
  cases d with
  | zero =>
    norm_num [ternary, Fintype.sum_prod_type, Fintype.sum_bool,
      Nat.doubleFactorial, ENNReal.mul_inv_cancel]
  | succ d =>
    have he : 2 * (d + 1) ≠ 0 := by omega
    have hm : (Fintype.card ternary.Seed : ℝ≥0∞)⁻¹ *
        ∑ s, (ternary.value s |>.natAbs : ℝ≥0∞) ^ (2 * (d + 1)) = 1 / 2 := by
      change (Fintype.card (Bool × Bool) : ℝ≥0∞)⁻¹ *
        (∑ s : Bool × Bool, (sparseBit s |>.natAbs : ℝ≥0∞) ^ (2 * (d + 1))) = _
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.sum_prod_type,
        Fintype.sum_bool, sparseBit]
      norm_num [he]
      rw [show (2 : ℝ≥0∞) = 1 + 1 by norm_num, mul_add, mul_one,
        quarter_add_quarter]
      norm_num
    rw [hm]
    simpa using ternary_gaussian_bound d
/-- The uniform entry law is symmetric. -/
theorem uniform_symmetric (b : ℕ) : (uniform b).Symmetric := by
  intro z
  rw [uniform_apply, uniform_apply]
  congr 1
  exact propext (by omega)
/-- Under `uniform b`, every set of integers with no two consecutive elements has probability at
most `(b + 1) / (2 * b + 1)`. -/
theorem uniform_noTwoConsecutiveBound (b : ℕ) :
    (uniform b).NoTwoConsecutiveBound ((b + 1 : ℝ≥0∞) / (2 * b + 1)) := by
  classical
  intro P hP
  let f : {s : Fin (2 * b + 1) // (s.val : ℤ) - b ∈ P} → Fin (b + 1) :=
    fun s => ⟨s.val.val / 2, by have := s.val.isLt; omega⟩
  have hf : Function.Injective f := by
    intro s t hst
    have hh : s.val.val / 2 = t.val.val / 2 := congrArg Fin.val hst
    have hs := s.val.isLt
    have ht := t.val.isLt
    apply Subtype.ext
    apply Fin.ext
    by_contra hne
    have hd : s.val.val + 1 = t.val.val ∨ t.val.val + 1 = s.val.val := by omega
    rcases hd with hd | hd
    · have hz : (t.val.val : ℤ) - b = ((s.val.val : ℤ) - b) + 1 := by omega
      exact hP _ s.property (hz ▸ t.property)
    · have hz : (s.val.val : ℤ) - b = ((t.val.val : ℤ) - b) + 1 := by omega
      exact hP _ t.property (hz ▸ s.property)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  change eventProbability ((PMF.uniformOfFintype (Fin (2 * b + 1))).map
    (fun s => (s.val : ℤ) - b)) (· ∈ P) ≤ _
  rw [Probability.eventProbability_map_uniform_eq_card]
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast hc
/-- Under `uniform b`, every integer has mass at most `1 / (2 * b + 1)`. -/
theorem uniform_atomBound (b : ℕ) : (uniform b).AtomBound (1 / (2 * b + 1)) := by
  intro z
  rw [uniform_apply, one_div]
  split_ifs <;> simp
/-- The even moments of `uniform b` are at most those of a centered Gaussian of variance
`b * (b + 1) / 3`. -/
theorem uniform_momentDominated (b : ℕ) : (uniform b).MomentDominated ((b * (b + 1) : ℕ) / 3) :=
  by
  intro d
  cases d with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, Nat.zero_sub, Nat.doubleFactorial, mul_one]
    unfold expectation
    simp
  | succ d =>
    have hvar : ((((b * (b + 1) : ℕ) : ℝ≥0) / 3 : ℝ≥0) : ℝ≥0∞) =
        ((b : ℝ≥0∞) * (b + 1)) / 3 := by
      simp only [ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_natCast,
        ENNReal.coe_ofNat, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hb : (b : ℝ≥0∞) ^ 2 ≤
        3 * ((((b * (b + 1) : ℕ) : ℝ≥0) / 3 : ℝ≥0) : ℝ≥0∞) := by
      rw [hvar, mul_comm 3, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
      simpa only [pow_two] using
        mul_le_mul_right (show (b : ℝ≥0∞) ≤ b + 1 from le_self_add) (b : ℝ≥0∞)
    have hfac : (3 : ℝ≥0∞) ^ d ≤ (Nat.doubleFactorial (2 * d + 1) : ℝ≥0∞) := by
      exact_mod_cast doubleFactorial_ge_three_pow d
    have he : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
    rw [he]
    calc
      _ ≤ (b : ℝ≥0∞) ^ (2 * d) *
          ((((b * (b + 1) : ℕ) : ℝ≥0) / 3 : ℝ≥0) : ℝ≥0∞) := by
        have hm := bounded_seed_moment (uniform b) d
        rw [uniform_second_moment] at hm
        exact hm
      _ = ((b : ℝ≥0∞) ^ 2) ^ d *
          ((((b * (b + 1) : ℕ) : ℝ≥0) / 3 : ℝ≥0) : ℝ≥0∞) := by rw [pow_mul]
      _ ≤ (3 * ((((b * (b + 1) : ℕ) : ℝ≥0) / 3 : ℝ≥0) : ℝ≥0∞)) ^ d *
          ((((b * (b + 1) : ℕ) : ℝ≥0) / 3 : ℝ≥0) : ℝ≥0∞) :=
        mul_le_mul_left (pow_le_pow_left' hb d) _
      _ = (3 : ℝ≥0∞) ^ d *
          ((((b * (b + 1) : ℕ) : ℝ≥0) / 3 : ℝ≥0) : ℝ≥0∞) ^ (d + 1) := by
        rw [mul_pow, pow_succ, mul_assoc]
      _ ≤ _ := mul_le_mul_left hfac _
end EntryLaw

end CertifiedProjections.MultiStage
