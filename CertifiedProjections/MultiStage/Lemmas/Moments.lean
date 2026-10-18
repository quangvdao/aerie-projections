/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Stage
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen

/-!
# Squared-norm moments of one stage

The main result is `stage_moment_le`: for a symmetric entry law `μ` with `μ.MomentDominated s2`, a
stage with `c` rows maps a table `X` to a table `Y` whose squared norm has `t`-th moment at most
`s2 ^ t * chiSquareMoment c t * sqNorm X ^ t`. Here `chiSquareMoment c t` is the `t`-th moment of a
chi-square variable with `c` degrees of freedom.

The proof bounds the even moments of one output entry by induction on the fan-in
(`moment_row_scalar`), combines the columns of one output row by convexity (`moment_sum_columns`),
and combines the `c` independent rows by the binomial identity `chiSquareMoment_add`
(`realAverage_rows_bound`).

Spec Lemma 5.1.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}

/-- The `t`-th moment of a chi-square variable with `c` degrees of freedom: `∏ j < t, (c + 2 j)`.
Spec Lemma 5.1. -/
def chiSquareMoment (c t : ℕ) : ℕ := ∏ j ∈ Finset.range t, (c + 2 * j)
/-- `chiSquareMoment c (t + 1)` is `chiSquareMoment c t * (c + 2 * t)`. -/
private lemma chiSquareMoment_succ (c t : ℕ) :
    chiSquareMoment c (t + 1) = chiSquareMoment c t * (c + 2 * t) := by
  simp [chiSquareMoment, Finset.prod_range_succ]

/-- The binomial identity for chi-square moments, as a sum over pairs `ij` with `ij.1 + ij.2 = t`:
the sum of `t.choose ij.1 * (chiSquareMoment c ij.1 * chiSquareMoment d ij.2)` is
`chiSquareMoment (c + d) t`. -/
private lemma chiSquareMoment_add_antidiagonal (c d t : ℕ) :
    (∑ ij ∈ Finset.antidiagonal t, t.choose ij.1 *
      (chiSquareMoment c ij.1 * chiSquareMoment d ij.2)) = chiSquareMoment (c + d) t := by
  induction t with
  | zero => simp [chiSquareMoment]
  | succ t ih =>
    have hsplit := Finset.sum_antidiagonal_choose_succ_mul (R := ℕ)
      (fun i j => chiSquareMoment c i * chiSquareMoment d j) t
    simp only [Nat.cast_id] at hsplit
    rw [hsplit]
    simp_rw [chiSquareMoment_succ]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ ij ∈ Finset.antidiagonal t, (c + d + 2 * t) *
          (t.choose ij.1 * (chiSquareMoment c ij.1 * chiSquareMoment d ij.2)) := by
        apply Finset.sum_congr rfl
        intro ij hij
        have ht : ij.1 + ij.2 = t := Finset.mem_antidiagonal.mp hij
        have hc : t.choose ij.2 = t.choose ij.1 := (Nat.choose_symm_of_eq_add ht.symm).symm
        rw [hc, ← ht]
        ring
      _ = (c + d + 2 * t) * chiSquareMoment (c + d) t := by
        rw [← Finset.mul_sum, ih]
      _ = _ := by ring

/-- The binomial identity for chi-square moments, as a sum over `k ≤ t`: the sum of
`t.choose k * chiSquareMoment c k * chiSquareMoment d (t - k)` is `chiSquareMoment (c + d) t`. -/
private lemma chiSquareMoment_add (c d t : ℕ) :
    (∑ k ∈ Finset.range (t + 1), t.choose k * chiSquareMoment c k *
      chiSquareMoment d (t - k)) = chiSquareMoment (c + d) t := by
  have h := chiSquareMoment_add_antidiagonal c d t
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => t.choose i * (chiSquareMoment c i * chiSquareMoment d j)) t] at h
  simpa only [mul_assoc] using h

/-- The expectation of `g` under `stage μ c X` is the average, over all seed matrices `s`, of `g`
applied to the product of the matrix of values `μ.value (s i j)` with `X`. -/
private theorem stage_expectation_seed (μ : EntryLaw) (c : ℕ) (X : Table f F)
    (g : Table c F → ℝ≥0∞) :
    expectation (stage μ c X) g =
      (Fintype.card (Fin c → Fin f → μ.Seed) : ℝ≥0∞)⁻¹ *
        ∑ s : Fin c → Fin f → μ.Seed,
          g (Matrix.of (fun i j => μ.value (s i j)) * X) := by
  rw [stage, expectation_map, EntryLaw.matrixPMF, uniformPiMap, expectation_map]
  unfold uniformPiPMF
  convert expectation_uniformOfFintype (α := Fin c → Fin f → μ.Seed)
    (fun s => g (Matrix.of (fun i j => μ.value (s i j)) * X)) using 1
  congr 1
  congr 1
  exact Subsingleton.elim _ _

/-- `chiSquareMoment 1 t` is the double factorial of `2 * t - 1`. -/
private theorem chiSquareMoment_one (t : ℕ) :
    chiSquareMoment 1 t = Nat.doubleFactorial (2 * t - 1) := by
  cases t with
  | zero => simp [chiSquareMoment]
  | succ t =>
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega,
      Nat.doubleFactorial_eq_prod_odd]
    unfold chiSquareMoment
    rw [Finset.prod_range_succ']
    simp only [mul_zero, add_zero, mul_one]
    apply Finset.prod_congr rfl
    intro i hi
    omega

/-- The average of `g` over the finite type `A`. -/
private noncomputable def realAverage {A : Type*} [Fintype A] (g : A → ℝ) : ℝ :=
  (Fintype.card A : ℝ)⁻¹ * ∑ a, g a

/-- The average of a finite sum of functions is the sum of their averages. -/
private lemma realAverage_sum {A B : Type*} [Fintype A]
    (s : Finset B) (g : B → A → ℝ) :
    realAverage (fun a => ∑ b ∈ s, g b a) = ∑ b ∈ s, realAverage (g b) := by
  unfold realAverage
  rw [Finset.sum_comm, Finset.mul_sum]

/-- A constant factor `r` on the right can be taken out of an average. -/
private lemma realAverage_mul_const {A : Type*} [Fintype A] (g : A → ℝ) (r : ℝ) :
    realAverage (fun a => g a * r) = realAverage g * r := by
  simp only [realAverage, ← Finset.sum_mul, mul_assoc]

/-- A constant factor `r` on the left can be taken out of an average. -/
private lemma realAverage_const_mul {A : Type*} [Fintype A] (g : A → ℝ) (r : ℝ) :
    realAverage (fun a => r * g a) = r * realAverage g := by
  simp only [realAverage, ← Finset.mul_sum]
  ring

/-- The average of a nonnegative function is nonnegative. -/
private lemma realAverage_nonneg {A : Type*} [Fintype A] (g : A → ℝ)
    (hg : ∀ a, 0 ≤ g a) : 0 ≤ realAverage g := by
  unfold realAverage
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun a _ => hg a)

/-- The average over `A × B` is the average over `a : A` of the average over `b : B`. -/
private lemma realAverage_prod {A B : Type*} [Fintype A] [Fintype B]
    (g : A × B → ℝ) :
    realAverage g = realAverage (fun a => realAverage (fun b => g (a, b))) := by
  simp only [realAverage, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The average over tuples of length `c + 1` is the average over the first entry `a` of the average
over the remaining entries `s`. -/
private lemma realAverage_cons {A : Type*} [Fintype A] (c : ℕ)
    (g : (Fin (c + 1) → A) → ℝ) :
    realAverage g = realAverage (fun a => realAverage (fun s => g (Fin.cons a s))) := by
  let e := Fin.consEquiv (fun _ : Fin (c + 1) => A)
  have he : realAverage (fun p : A × (Fin c → A) => g (e p)) = realAverage g := by
    simp only [realAverage, Fintype.card_congr e, e.sum_comp]
  rw [← he, realAverage_prod]
  rfl

/-- Binomial expansion after splitting off one entry: the average of `(∑ i, W (s i)) ^ t` over
tuples `s` of length `c + 1` is the sum over `k ≤ t` of `t.choose k` times the average of
`(∑ i, W (s i)) ^ k` over tuples of length `c` times the average of `W a ^ (t - k)`. -/
private lemma realAverage_row_convolution {A : Type*} [Fintype A] (W : A → ℝ)
    (c t : ℕ) :
    realAverage (fun s : Fin (c + 1) → A => (∑ i, W (s i)) ^ t) =
    ∑ k ∈ Finset.range (t + 1), (t.choose k : ℝ) *
      realAverage (fun s : Fin c → A => (∑ i, W (s i)) ^ k) *
      realAverage (fun a => W a ^ (t - k)) := by
  rw [realAverage_cons]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp_rw [add_comm (W _), add_pow, realAverage_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [realAverage_mul_const]
  rw [realAverage_const_mul]
  ring

/-- If `W` is nonnegative and, for every `t`, the average of `W a ^ t` is at most
`chiSquareMoment 1 t * q ^ t`, then the average of `(∑ i, W (s i)) ^ t` over tuples `s` of length
`c` is at most `chiSquareMoment c t * q ^ t`. -/
private theorem realAverage_rows_bound {A : Type*} [Fintype A] [Nonempty A]
    (W : A → ℝ) (hWnonneg : ∀ a, 0 ≤ W a) (q : ℝ) (hq : 0 ≤ q)
    (hW : ∀ t, realAverage (fun a => W a ^ t) ≤ (chiSquareMoment 1 t : ℝ) * q ^ t) :
    ∀ c t, realAverage (fun s : Fin c → A => (∑ i, W (s i)) ^ t) ≤
      (chiSquareMoment c t : ℝ) * q ^ t := by
  have hconv (c t : ℕ) :
      (∑ k ∈ Finset.range (t + 1), (t.choose k : ℝ) *
        (chiSquareMoment c k : ℝ) * (chiSquareMoment 1 (t - k) : ℝ)) =
        (chiSquareMoment (c + 1) t : ℝ) := by
    exact_mod_cast chiSquareMoment_add c 1 t
  intro c
  induction c with
  | zero =>
    intro t
    cases t with
    | zero => simp [realAverage, chiSquareMoment]
    | succ t =>
      have hz : chiSquareMoment 0 (t + 1) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.zero_lt_succ t))
        simp
      simp [realAverage, hz]
  | succ c ih =>
    intro t
    rw [realAverage_row_convolution]
    calc
      _ ≤ ∑ k ∈ Finset.range (t + 1), (t.choose k : ℝ) *
          ((chiSquareMoment c k : ℝ) * q ^ k) *
          ((chiSquareMoment 1 (t - k) : ℝ) * q ^ (t - k)) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (ih k) (Nat.cast_nonneg _)
        · exact hW (t - k)
        · exact realAverage_nonneg _ fun a => pow_nonneg (hWnonneg a) (t - k)
        · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
            (Nat.cast_nonneg _) (pow_nonneg hq k))
      _ = (chiSquareMoment (c + 1) t : ℝ) * q ^ t := by
        rw [← hconv c t, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hp : q ^ k * q ^ (t - k) = q ^ t := by
          rw [← pow_add, Nat.add_sub_of_le hk']
        calc
          _ = (t.choose k : ℝ) * (chiSquareMoment c k : ℝ) *
              (chiSquareMoment 1 (t - k) : ℝ) * (q ^ k * q ^ (t - k)) := by ring
          _ = _ := by rw [hp]

/-- The average of the constant `v` over a nonempty finite type is `v`. -/
private theorem realAverage_const {α : Type*} [Fintype α] [Nonempty α] (v : ℝ) :
    realAverage (fun _a : α => v) = v := by
  simp [realAverage, Fintype.card_ne_zero]

/-- The average over `α × β` of `u a.1 * v a.2` is the product of the averages of `u` and `v`. -/
private theorem realAverage_mul_independent {α β : Type*} [Fintype α] [Fintype β]
    (u : α → ℝ) (v : β → ℝ) :
    realAverage (fun a : α × β => u a.1 * v a.2) = realAverage u * realAverage v := by
  simp only [realAverage, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The average of `v` over seed vectors of length `f + 1` is the average over pairs of a first seed
and a seed vector of length `f`. -/
private theorem realAverage_fin_succ (μ : EntryLaw) (f : ℕ)
    (v : (Fin (f + 1) → μ.Seed) → ℝ) :
    realAverage v = realAverage (fun a : μ.Seed × (Fin f → μ.Seed) => v (Fin.cons a.1 a.2)) := by
  let e := Fin.consEquiv (fun _ : Fin (f + 1) => μ.Seed)
  have hsum := e.sum_comp v
  have hcard := Fintype.card_congr e
  change (Fintype.card (Fin (f + 1) → μ.Seed) : ℝ)⁻¹ * ∑ a, v a =
    (Fintype.card (μ.Seed × (Fin f → μ.Seed)) : ℝ)⁻¹ *
      ∑ a : μ.Seed × (Fin f → μ.Seed), v (Fin.cons a.1 a.2)
  rw [← hcard]
  congr 1
  simpa only [e, Fin.consEquiv, Equiv.coe_fn_mk] using hsum.symm

/-- Binomial expansion of the average over `α × β` of `(u a.1 + v a.2) ^ n`: the sum over `k ≤ n` of
`n.choose k` times the average of `u a ^ k` times the average of `v b ^ (n - k)`. -/
private theorem realAverage_add_pow_independent {α β : Type*} [Fintype α] [Fintype β]
    (u : α → ℝ) (v : β → ℝ) (n : ℕ) :
    realAverage (fun a : α × β => (u a.1 + v a.2) ^ n) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        realAverage (fun a => u a ^ k) * realAverage (fun b => v b ^ (n - k)) := by
  simp_rw [add_pow]
  rw [realAverage_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [realAverage_mul_const,
    realAverage_mul_independent (fun a => u a ^ k) (fun b => v b ^ (n - k))]
  ring

/-- If `A` is zero at every odd index, the sum of `A k` over `k ≤ 2 * t` is the sum of `A (2 * i)`
over `i ≤ t`. -/
private lemma sum_even_range (A : ℕ → ℝ) (hA : ∀ i, A (2 * i + 1) = 0) (t : ℕ) :
    ∑ k ∈ Finset.range (2 * t + 1), A k = ∑ i ∈ Finset.range (t + 1), A (2 * i) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, hA, add_zero,
      show 2 * t + 1 + 1 = 2 * (t + 1) by omega]
    exact (Finset.sum_range_succ (fun i => A (2 * i)) (t + 1)).symm

/-- The factorial of `2 * n` is `chiSquareMoment 1 n * 2 ^ n * n.factorial`. -/
private lemma factorial_two_mul_eq (n : ℕ) :
    (2 * n).factorial = chiSquareMoment 1 n * 2 ^ n * n.factorial := by
  induction n with
  | zero => simp [chiSquareMoment]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, ih]
    simp only [chiSquareMoment, Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
    ring

/-- For `i ≤ t`, the product
`(2 * t).choose (2 * i) * chiSquareMoment 1 (t - i) * chiSquareMoment 1 i` is
`chiSquareMoment 1 t * t.choose i`. -/
private lemma even_choose (t i : ℕ) (hi : i ≤ t) :
    (2 * t).choose (2 * i) * chiSquareMoment 1 (t - i) * chiSquareMoment 1 i =
      chiSquareMoment 1 t * t.choose i := by
  have hi2 : 2 * i ≤ 2 * t := by omega
  have hsub : 2 * t - 2 * i = 2 * (t - i) := by omega
  have hsum : i + (t - i) = t := Nat.add_sub_of_le hi
  have hpow : 2 ^ t = 2 ^ i * 2 ^ (t - i) := by rw [← pow_add, hsum]
  have hp : 0 < 2 ^ t * i.factorial * (t - i).factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hp
  calc
    _ = (2 * t).choose (2 * i) *
        (chiSquareMoment 1 i * 2 ^ i * i.factorial) *
        (chiSquareMoment 1 (t - i) * 2 ^ (t - i) * (t - i).factorial) := by
      rw [hpow]
      ring
    _ = (2 * t).factorial := by
      rw [← factorial_two_mul_eq i, ← factorial_two_mul_eq (t - i), ← hsub]
      exact Nat.choose_mul_factorial_mul_factorial hi2
    _ = chiSquareMoment 1 t * 2 ^ t * t.factorial := factorial_two_mul_eq t
    _ = _ := by
      rw [← Nat.choose_mul_factorial_mul_factorial hi]
      ring

/-- The identity `even_choose` with both sides cast to `ℝ`. -/
private lemma even_choose_real (t i : ℕ) (hi : i ≤ t) :
    ((2 * t).choose (2 * i) : ℝ) * (chiSquareMoment 1 (t - i) : ℝ) *
        (chiSquareMoment 1 i : ℝ) = (chiSquareMoment 1 t : ℝ) * (t.choose i : ℝ) := by
  exact_mod_cast even_choose t i hi

/-- The mass of `z` under `μ.entryPMF`, as a real number, is the number of seeds with value `z`
divided by the number of seeds. -/
private theorem entry_mass (μ : EntryLaw) (z : ℤ) :
    (μ.entryPMF z).toReal = (Fintype.card μ.Seed : ℝ)⁻¹ *
      ((Finset.univ.filter fun a => μ.value a = z).card : ℝ) := by
  classical
  rw [EntryLaw.entryPMF, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  have h :
      (∑ a : μ.Seed, if z = μ.value a then
        (Fintype.card μ.Seed : ℝ≥0∞)⁻¹ else 0) =
      (Fintype.card μ.Seed : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun a => μ.value a = z).card : ℝ≥0∞) := by
    rw [← Finset.sum_boole]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : μ.value a = z
    · simp [ha]
    · simp [ha, Ne.symm ha]
  rw [h]
  simp

/-- If the finite set `s` contains every value of `μ`, the average of `h (μ.value a)` over seeds `a`
is the sum over `z ∈ s` of the mass of `z` under `μ.entryPMF` times `h z`. -/
private theorem avg_value_sum (μ : EntryLaw) (s : Finset ℤ)
    (hmem : ∀ a, μ.value a ∈ s) (h : ℤ → ℝ) :
    realAverage (fun a : μ.Seed => h (μ.value a)) =
      ∑ z ∈ s, (μ.entryPMF z).toReal * h z := by
  classical
  simp_rw [entry_mass]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  unfold realAverage
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := s)
    (g := μ.value) (fun a _ => hmem a) (fun a => h (μ.value a))]
  apply Finset.sum_congr rfl
  intro z _
  rw [show (∑ a ∈ Finset.univ.filter (fun a => μ.value a = z), h (μ.value a)) =
      ∑ _a ∈ Finset.univ.filter (fun a => μ.value a = z), h z by
    apply Finset.sum_congr rfl
    intro a ha
    rw [(Finset.mem_filter.mp ha).2]]
  simp

/-- For a symmetric entry law, the average over seeds of an odd power of the value is zero. -/
private theorem avg_value_odd (μ : EntryLaw) (hsymm : μ.Symmetric) (d : ℕ) :
    realAverage (fun a : μ.Seed => (μ.value a : ℝ) ^ (2 * d + 1)) = 0 := by
  classical
  let s : Finset ℤ := Finset.univ.image μ.value ∪ Finset.univ.image (fun a => -μ.value a)
  have hmem (a : μ.Seed) : μ.value a ∈ s := by simp [s]
  rw [avg_value_sum μ s hmem (fun z => (z : ℝ) ^ (2 * d + 1))]
  have hn (z : ℤ) : z ∈ s ↔ -z ∈ s := by
    simp only [s, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact Or.inr ⟨a, rfl⟩
      · exact Or.inl ⟨a, by simp⟩
    · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
      · exact Or.inr ⟨a, by simpa using congrArg Neg.neg ha⟩
      · exact Or.inl ⟨a, by simpa using congrArg Neg.neg ha⟩
  have hneg :
      (∑ z ∈ s, (μ.entryPMF z).toReal * (z : ℝ) ^ (2 * d + 1)) =
        -∑ z ∈ s, (μ.entryPMF z).toReal * (z : ℝ) ^ (2 * d + 1) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_equiv (Equiv.neg ℤ) hn
    intro z _
    simp only [Equiv.neg_apply, hsymm z, Int.cast_neg]
    simp [pow_add, pow_mul]
  linarith

/-- If `μ.MomentDominated s2` holds, the average over seeds of the `2 * d`-th power of the value is
at most `chiSquareMoment 1 d * s2 ^ d`. -/
private theorem avg_value_even (μ : EntryLaw) {s2 : ℝ≥0}
    (hs : μ.MomentDominated s2) (d : ℕ) :
    realAverage (fun a : μ.Seed => (μ.value a : ℝ) ^ (2 * d)) ≤
      (chiSquareMoment 1 d : ℝ) * (s2 : ℝ) ^ d := by
  have h := hs d
  have hmap : expectation μ.entryPMF (fun z => (z.natAbs : ℝ≥0∞) ^ (2 * d)) =
      (Fintype.card μ.Seed : ℝ≥0∞)⁻¹ *
        ∑ a, ((μ.value a).natAbs : ℝ≥0∞) ^ (2 * d) := by
    unfold expectation EntryLaw.entryPMF
    simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp [tsum_fintype, PMF.uniformOfFintype_apply, Finset.mul_sum]
  rw [hmap] at h
  have hh := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.coe_toReal] at hh
  rw [ENNReal.toReal_sum (by intros; finiteness)] at hh
  simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast] at hh
  have hpow (a : μ.Seed) : ((μ.value a).natAbs : ℝ) ^ (2 * d) =
      (μ.value a : ℝ) ^ (2 * d) := by
    rw [pow_mul, pow_mul]
    congr 1
    simp
  simp_rw [hpow] at hh
  simpa [realAverage, chiSquareMoment_one] using hh

/-- For a symmetric entry law with `μ.MomentDominated s2` and a real vector `x`, the average over
seed vectors `a` of the `2 * t`-th power of `∑ k, μ.value (a k) * x k` is at most
`chiSquareMoment 1 t * s2 ^ t * (∑ k, x k ^ 2) ^ t`. -/
private theorem moment_row_scalar (μ : EntryLaw) (hsymm : μ.Symmetric) {s2 : ℝ≥0}
    (hs : μ.MomentDominated s2) (f t : ℕ) (x : Fin f → ℝ) :
    realAverage (fun a : Fin f → μ.Seed => (∑ k, (μ.value (a k) : ℝ) * x k) ^ (2 * t)) ≤
      (chiSquareMoment 1 t : ℝ) * (s2 : ℝ) ^ t * (∑ k, x k ^ 2) ^ t := by
  induction f generalizing t with
  | zero =>
    cases t with
    | zero => simp [realAverage_const, chiSquareMoment]
    | succ t => simp [realAverage_const]
  | succ f ih =>
    let u : μ.Seed → ℝ := fun a => (μ.value a : ℝ) * x 0
    let v : (Fin f → μ.Seed) → ℝ :=
      fun a => ∑ k, (μ.value (a k) : ℝ) * x k.succ
    let N : ℝ := ∑ k : Fin f, x k.succ ^ 2
    have hN : 0 ≤ N := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hcoord (a : μ.Seed × (Fin f → μ.Seed)) :
        (∑ k : Fin (f + 1),
          (μ.value ((Fin.cons a.1 a.2 : Fin (f + 1) → μ.Seed) k) : ℝ) * x k) =
          u a.1 + v a.2 := by
      simp [Fin.sum_univ_succ, u, v]
    rw [realAverage_fin_succ μ f]
    simp_rw [hcoord]
    rw [realAverage_add_pow_independent]
    have huodd (i : ℕ) : realAverage (fun a => u a ^ (2 * i + 1)) = 0 := by
      simp_rw [u, mul_pow]
      rw [realAverage_mul_const, avg_value_odd μ hsymm, zero_mul]
    rw [sum_even_range _ (fun i => by rw [huodd]; ring)]
    have hueven (i : ℕ) :
        realAverage (fun a => u a ^ (2 * i)) ≤
          (chiSquareMoment 1 i : ℝ) * (s2 : ℝ) ^ i * (x 0 ^ 2) ^ i := by
      simp_rw [u, mul_pow]
      rw [realAverage_mul_const, show x 0 ^ (2 * i) = (x 0 ^ 2) ^ i by rw [pow_mul]]
      exact mul_le_mul_of_nonneg_right (avg_value_even μ hs i) (by positivity)
    have hveven (i : ℕ) :
        realAverage (fun a => v a ^ (2 * i)) ≤
          (chiSquareMoment 1 i : ℝ) * (s2 : ℝ) ^ i * N ^ i :=
      ih i (fun k => x k.succ)
    calc
      _ ≤ ∑ i ∈ Finset.range (t + 1),
          ((2 * t).choose (2 * i) : ℝ) *
            ((chiSquareMoment 1 i : ℝ) * (s2 : ℝ) ^ i * (x 0 ^ 2) ^ i) *
            ((chiSquareMoment 1 (t - i) : ℝ) * (s2 : ℝ) ^ (t - i) * N ^ (t - i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ t := by simpa using Finset.mem_range.mp hi
        rw [show 2 * t - 2 * i = 2 * (t - i) by omega]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hueven i) (by positivity)
        · exact hveven (t - i)
        · exact realAverage_nonneg _ (fun a => by
            rw [pow_mul]
            exact pow_nonneg (sq_nonneg _) _)
        · positivity
      _ = (chiSquareMoment 1 t : ℝ) * (s2 : ℝ) ^ t * (∑ k, x k ^ 2) ^ t := by
        rw [Fin.sum_univ_succ]
        change _ = (chiSquareMoment 1 t : ℝ) * (s2 : ℝ) ^ t * (x 0 ^ 2 + N) ^ t
        rw [add_pow]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ t := by simpa using Finset.mem_range.mp hi
        have hp : (s2 : ℝ) ^ i * (s2 : ℝ) ^ (t - i) = (s2 : ℝ) ^ t := by
          rw [← pow_add, Nat.add_sub_of_le hi']
        have hc := even_choose_real t i hi'
        calc
          _ = (((2 * t).choose (2 * i) : ℝ) * (chiSquareMoment 1 (t - i) : ℝ) *
              (chiSquareMoment 1 i : ℝ)) * ((s2 : ℝ) ^ i * (s2 : ℝ) ^ (t - i)) *
              ((x 0 ^ 2) ^ i * N ^ (t - i)) := by ring
          _ = _ := by rw [hc, hp]; ring

/-- Let `0 < t`, let `z a j` and `w j` be nonnegative, and let `z a j = 0` whenever `w j = 0`. If
for every `j` the average over `a` of `z a j ^ t` is at most `K * w j ^ t`, then the average over
`a` of `(∑ j, z a j) ^ t` is at most `K * (∑ j, w j) ^ t`. -/
private theorem moment_sum_columns {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] (z : A → B → ℝ) (w : B → ℝ) (K : ℝ) (t : ℕ)
    (ht : 0 < t) (hz : ∀ a j, 0 ≤ z a j) (hw : ∀ j, 0 ≤ w j)
    (hzero : ∀ j, w j = 0 → ∀ a, z a j = 0)
    (hm : ∀ j, (Fintype.card A : ℝ)⁻¹ * ∑ a, z a j ^ t ≤ K * w j ^ t) :
    (Fintype.card A : ℝ)⁻¹ * ∑ a, (∑ j, z a j) ^ t ≤ K * (∑ j, w j) ^ t := by
  classical
  let N := ∑ j, w j
  have hN : 0 ≤ N := Finset.sum_nonneg fun j _ => hw j
  by_cases hN0 : N = 0
  · have hw0 : ∀ j, w j = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw j)).mp hN0
      exact fun j => h j (Finset.mem_univ j)
    simp [hzero _ (hw0 _), show (∑ j, w j) = 0 from hN0, ne_of_gt ht]
  have hNp : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
  have hj (a : A) : (∑ j, z a j) ^ t ≤
      N ^ t * ∑ j, (w j / N) * (z a j / w j) ^ t := by
    have h := (convexOn_pow (𝕜 := ℝ) t).map_sum_le
      (t := Finset.univ) (w := fun j => w j / N) (p := fun j => z a j / w j)
      (fun j _ => div_nonneg (hw j) hN)
      (by rw [← Finset.sum_div]; exact div_self hN0)
      (fun j _ => div_nonneg (hz a j) (hw j))
    simp only [smul_eq_mul] at h
    have he : ∑ j, w j / N * (z a j / w j) = (∑ j, z a j) / N := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj0 : w j = 0
      · simp [hj0, hzero j hj0 a]
      · field_simp
    rw [he, div_pow] at h
    simpa only [mul_comm] using (div_le_iff₀ (pow_pos hNp t)).mp h
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ a,
        N ^ t * ∑ j, (w j / N) * (z a j / w j) ^ t := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hj a) (by positivity)
    _ = N ^ t * ∑ j, (w j / N) *
        (((Fintype.card A : ℝ)⁻¹ * ∑ a, z a j ^ t) / w j ^ t) := by
      simp_rw [div_pow, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ N ^ t * ∑ j, (w j / N) * K := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hN t)
      apply Finset.sum_le_sum
      intro j _
      by_cases hj0 : w j = 0
      · simp [hj0]
      · apply mul_le_mul_of_nonneg_left _ (div_nonneg (hw j) hN)
        exact (div_le_iff₀ (pow_pos (lt_of_le_of_ne (hw j) (Ne.symm hj0)) t)).mpr (hm j)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_div, show ∑ j, w j = N from rfl,
        div_self hN0]
      ring

/-- If the bound of `moment_row_scalar` holds for every integer vector `x` (hypothesis `hm`), then
the average over seed vectors `a` of the `t`-th power of `∑ j, (∑ k, μ.value (a k) * X k j) ^ 2`,
the squared norm of one output row, is at most `chiSquareMoment 1 t * (s2 * sqNorm X) ^ t`. -/
private theorem moment_row_columns (μ : EntryLaw) (s2 : ℝ≥0) (X : Table f F)
    (hm : ∀ (t : ℕ) (x : Fin f → ℤ),
      (Fintype.card (Fin f → μ.Seed) : ℝ)⁻¹ *
        ∑ a : Fin f → μ.Seed, (∑ k, (μ.value (a k) : ℝ) * (x k : ℝ)) ^ (2 * t) ≤
      (chiSquareMoment 1 t : ℝ) * (s2 : ℝ) ^ t * (∑ k, (x k : ℝ) ^ 2) ^ t)
    (t : ℕ) :
    (Fintype.card (Fin f → μ.Seed) : ℝ)⁻¹ *
      ∑ a : Fin f → μ.Seed, (∑ j, (∑ k, (μ.value (a k) : ℝ) * (X k j : ℝ)) ^ 2) ^ t ≤
      (chiSquareMoment 1 t : ℝ) * ((s2 : ℝ) * (sqNorm X : ℝ)) ^ t := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [chiSquareMoment, Fintype.card_ne_zero]
  have hzero (j : Fin F) (hj : ∑ k, (X k j : ℝ) ^ 2 = 0) :
      ∀ a : Fin f → μ.Seed, (∑ k, (μ.value (a k) : ℝ) * (X k j : ℝ)) ^ 2 = 0 := by
    have hx : ∀ k, (X k j : ℝ) = 0 := by
      intro k
      exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sq_nonneg (X k j : ℝ))).mp hj k (Finset.mem_univ k))
    simp [hx]
  have h := moment_sum_columns
    (fun (a : Fin f → μ.Seed) j => (∑ k, (μ.value (a k) : ℝ) * (X k j : ℝ)) ^ 2)
    (fun j => ∑ k, (X k j : ℝ) ^ 2)
    ((chiSquareMoment 1 t : ℝ) * (s2 : ℝ) ^ t) t (Nat.pos_of_ne_zero ht)
    (fun _ _ => sq_nonneg _) (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hzero
    (fun j => by simpa only [← pow_mul] using hm t (fun k => X k j))
  rw [sqNorm_cast_real, Finset.sum_comm]
  simpa only [mul_pow, mul_assoc] using h

/-- If the average over seed matrices `a` of the `t`-th power of the squared norm of the stage
output is at most `chiSquareMoment c t * (s2 * sqNorm X) ^ t` as an inequality of real numbers
(hypothesis `h`), then the same bound holds for the expectation under `stage μ c X`. -/
private theorem stage_moment_le_of_real (μ : EntryLaw) (s2 : ℝ≥0) (c t : ℕ) (X : Table f F)
    (h : (Fintype.card (Fin c → Fin f → μ.Seed) : ℝ)⁻¹ *
      ∑ a : Fin c → Fin f → μ.Seed,
        (∑ i, ∑ j, (∑ k, (μ.value (a i k) : ℝ) * (X k j : ℝ)) ^ 2) ^ t ≤
      (chiSquareMoment c t : ℝ) * ((s2 : ℝ) * (sqNorm X : ℝ)) ^ t) :
    expectation (stage μ c X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ t) ≤
      (s2 : ℝ≥0∞) ^ t * (chiSquareMoment c t : ℝ≥0∞) * (sqNorm X : ℝ≥0∞) ^ t := by
  classical
  rw [stage_expectation_seed]
  have hcard : (Fintype.card (Fin c → Fin f → μ.Seed) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hcard)
      (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.pow_ne_top (by simp)))
    (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun _ _ => ENNReal.pow_ne_top (by simp))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.coe_toReal]
  simp_rw [sqNorm_cast_real, Matrix.mul_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul]
  simpa only [sqNorm_cast_real, mul_pow, mul_assoc, mul_comm, mul_left_comm] using h

/-- If the bound of `moment_row_scalar` holds for every integer vector `x` (hypothesis `hm`), then
the expectation of `sqNorm Y ^ t` over the output `Y` of `stage μ c X` is at most
`s2 ^ t * chiSquareMoment c t * sqNorm X ^ t`. -/
private theorem stage_moment_from_scalar (μ : EntryLaw) (s2 : ℝ≥0)
    (hm : ∀ (t : ℕ) (x : Fin f → ℤ),
      (Fintype.card (Fin f → μ.Seed) : ℝ)⁻¹ *
        ∑ a : Fin f → μ.Seed, (∑ k, (μ.value (a k) : ℝ) * (x k : ℝ)) ^ (2 * t) ≤
      (chiSquareMoment 1 t : ℝ) * (s2 : ℝ) ^ t * (∑ k, (x k : ℝ) ^ 2) ^ t)
    (c t : ℕ) (X : Table f F) :
    expectation (stage μ c X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ t) ≤
      (s2 : ℝ≥0∞) ^ t * (chiSquareMoment c t : ℝ≥0∞) * (sqNorm X : ℝ≥0∞) ^ t := by
  apply stage_moment_le_of_real μ s2 c t X
  exact realAverage_rows_bound
    (fun a : Fin f → μ.Seed => ∑ j, (∑ k, (μ.value (a k) : ℝ) * (X k j : ℝ)) ^ 2)
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) ((s2 : ℝ) * (sqNorm X : ℝ))
    (by positivity) (moment_row_columns μ s2 X hm) c t

/-- If the entry law `μ` is symmetric and `μ.MomentDominated s2` holds, then the expectation of
`sqNorm Y ^ t` over the output `Y` of `stage μ c X` is at most
`s2 ^ t * chiSquareMoment c t * sqNorm X ^ t`. Spec Lemma 5.1, with `(2 s²)^t (c/2)_t` written as
`s2 ^ t * chiSquareMoment c t`. -/
theorem stage_moment_le (μ : EntryLaw) (hsymm : μ.Symmetric) {s2 : ℝ≥0} (hs : μ.MomentDominated s2)
    (c t : ℕ) (X : Table f F) :
    expectation (stage μ c X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ t) ≤
      (s2 : ℝ≥0∞) ^ t * (chiSquareMoment c t : ℝ≥0∞) * (sqNorm X : ℝ≥0∞) ^ t := by
  exact stage_moment_from_scalar μ s2
    (fun d x => moment_row_scalar μ hsymm hs f d (fun k => (x k : ℝ))) c t X

end CertifiedProjections.MultiStage
