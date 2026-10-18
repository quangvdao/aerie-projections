/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Branch
import CertifiedProjections.MultiStage.Lemmas.Moments
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Moment bounds across stages

`MomentBound K t M` says that the table kernel `K` multiplies the `t`-th moment of the squared norm
by at most `M`. This file proves such a bound for one stage (`MomentBound.stage`), for a
deterministic map (`MomentBound.ofFun`), for sequential composition (`MomentBound.andThen`) and for
independent branches (`MomentBound.branches`, with the constant `branchMoment`), and derives the
tail bound `MomentBound.tail_le` from it (spec Theorem 7.1). `branchMoment_succ` is the recursion
of `branchMoment` in the number of branches, and `branchMomentTable` uses it to evaluate
natural-valued branch moments with lists (`branchMoment_eq_getD_branchMomentTable`).
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}
variable {f₁ F₁ f₂ F₂ t : ℕ} {M M₁ M₂ : ℝ≥0∞}
variable {K : TableKernel f F f' F'}
variable {K₁ : TableKernel f F f₁ F₁} {K₂ : TableKernel f₁ F₁ f₂ F₂}

/-- `K` multiplies the `t`-th moment of the squared norm by at most `M`: for every input table `X`,
the expectation of `sqNorm Y ^ t` over the output `Y` of `K X` is at most `M * sqNorm X ^ t`. -/
def MomentBound (K : TableKernel f F f' F') (t : ℕ) (M : ℝ≥0∞) : Prop :=
  ∀ X, expectation (K X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ t) ≤ M * (sqNorm X : ℝ≥0∞) ^ t

/-- Spec Theorem 7.1: `t! [u^t] (∑ k, m k u^k / k!)^g`, written as a multinomial sum: the sum, over
tuples `k : Fin g → ℕ` with entries summing to `t`, of the multinomial coefficient of `k` times
`∏ i, m (k i)`. This is the constant in the `t`-th moment bound for `g` independent branches when
each branch has `k`-th moment bound `m k`. -/
def branchMoment {R : Type*} [CommSemiring R] (g : ℕ) (m : ℕ → R) (t : ℕ) : R :=
  ∑ k ∈ Finset.Nat.antidiagonalTuple g t, (Nat.multinomial Finset.univ k : R) * ∏ i, m (k i)

/-- With no branches, `branchMoment 0 m t` is `1` if `t = 0` and `0` otherwise. -/
theorem branchMoment_zero {R : Type*} [CommSemiring R] (m : ℕ → R) (t : ℕ) :
    branchMoment 0 m t = if t = 0 then 1 else 0 := by
  cases t <;> simp [branchMoment]

/-- The multinomial coefficient of the tuple `Fin.cons i k` is `(i + ∑ j, k j).choose i` times the
multinomial coefficient of `k`. -/
private theorem multinomial_fin_cons (g i : ℕ) (k : Fin g → ℕ) :
    Nat.multinomial Finset.univ (Fin.cons i k) =
      (i + ∑ j, k j).choose i * Nat.multinomial Finset.univ k := by
  rw [Fin.univ_succ, Nat.multinomial_cons]
  simp only [Fin.cons_zero, Finset.sum_map, Function.Embedding.coeFn_mk, Fin.cons_succ]
  congr 1
  simp [Nat.multinomial]

/-- `branchMoment g m t` is the sum of the list of the terms `multinomial k * ∏ i, m (k i)` over
the tuples `k` of `List.Nat.antidiagonalTuple g t`. -/
private theorem branchMoment_eq_list_sum {R : Type*} [CommSemiring R]
    (g : ℕ) (m : ℕ → R) (t : ℕ) :
    branchMoment g m t = ((List.Nat.antidiagonalTuple g t).map
      (fun k => (Nat.multinomial Finset.univ k : R) * ∏ i, m (k i))).sum := by
  rfl

/-- `branchMoment (g + 1) m t` is the sum, over the pairs `(i, j)` with `i + j = t`, of
`t.choose i * (m i * branchMoment g m j)`. -/
theorem branchMoment_succ {R : Type*} [CommSemiring R]
    (g : ℕ) (m : ℕ → R) (t : ℕ) :
    branchMoment (g + 1) m t =
      ∑ ij ∈ Finset.antidiagonal t,
        (t.choose ij.1 : R) * (m ij.1 * branchMoment g m ij.2) := by
  classical
  rw [branchMoment_eq_list_sum, List.Nat.antidiagonalTuple, List.map_flatMap]
  change _ = ((List.Nat.antidiagonal t).map
    (fun ij => (t.choose ij.1 : R) * (m ij.1 * branchMoment g m ij.2))).sum
  rw [List.flatMap_def, List.sum_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ij hij
  simp only [List.map_map, Function.comp_def]
  have hij' : ij.1 + ij.2 = t := List.Nat.mem_antidiagonal.mp hij
  have hterm (k : Fin g → ℕ) (hk : k ∈ List.Nat.antidiagonalTuple g ij.2) :
      (Nat.multinomial Finset.univ (Fin.cons ij.1 k) : R) *
          ∏ i : Fin (g + 1), m ((Fin.cons ij.1 k : Fin (g + 1) → ℕ) i) =
        (t.choose ij.1 : R) * (m ij.1 *
          ((Nat.multinomial Finset.univ k : R) * ∏ i, m (k i))) := by
    rw [multinomial_fin_cons, List.Nat.mem_antidiagonalTuple.mp hk, hij', Nat.cast_mul,
      Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ac_rfl
  rw [List.map_congr_left hterm]
  rw [List.sum_map_mul_left, List.sum_map_mul_left, ← branchMoment_eq_list_sum]

/-- `branchMomentTable m bound g` is the list of the values `branchMoment g m s` for
`s = 0, …, bound` (`getD_branchMomentTable`). It is computed by the recursion `branchMoment_succ`,
with each binomial coefficient written as a quotient of factorials, so that the kernel can evaluate
it. -/
def branchMomentTable (m : ℕ → ℕ) (bound : ℕ) : ℕ → List ℕ
  | 0 => (List.range (bound + 1)).map (fun s => if s = 0 then 1 else 0)
  | g + 1 =>
    let prev := branchMomentTable m bound g
    (List.range (bound + 1)).map fun s =>
      ((List.range (s + 1)).map fun i =>
        s.factorial / (i.factorial * (s - i).factorial) *
          (m i * prev.getD (s - i) 0)).sum

/-- For `i < n`, the entry at index `i` of `(List.range n).map f` is `f i`. -/
private theorem getD_map_range (f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa)]
  simp

/-- For `s ≤ bound`, the entry at index `s` of `branchMomentTable m bound g` is
`branchMoment g m s`. -/
theorem getD_branchMomentTable (m : ℕ → ℕ) (bound g s : ℕ) (hs : s ≤ bound) :
    (branchMomentTable m bound g).getD s 0 = branchMoment g m s := by
  induction g generalizing s with
  | zero =>
    rw [branchMomentTable, getD_map_range _ _ _ (by omega), branchMoment_zero]
  | succ g ih =>
    rw [branchMomentTable, getD_map_range _ _ _ (by omega), branchMoment_succ,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ s := by simpa using hi
    rw [ih (s - i) (by omega), Nat.choose_eq_factorial_div_factorial hi']
    simp

/-- `branchMoment g m t` is the last entry of `branchMomentTable m t g`. -/
theorem branchMoment_eq_getD_branchMomentTable (g : ℕ) (m : ℕ → ℕ) (t : ℕ) :
    branchMoment g m t = (branchMomentTable m t g).getD t 0 :=
  (getD_branchMomentTable m t g t le_rfl).symm

/-- The multinomial theorem for a sum indexed by `Fin n`: `(∑ i, u i) ^ t` is the sum, over tuples
`k` with entries summing to `t`, of the multinomial coefficient of `k` times `∏ i, u i ^ k i`. -/
private theorem sum_pow_antidiagonalTuple {R : Type*} [CommSemiring R]
    {n : ℕ} (u : Fin n → R) (t : ℕ) :
    (∑ i, u i) ^ t = ∑ k ∈ Finset.Nat.antidiagonalTuple n t,
      (Nat.multinomial Finset.univ k : R) * ∏ i, u i ^ k i := by
  rw [Finset.sum_pow_eq_sum_piAntidiag,
    Finset.piAntidiag_univ_fin_eq_antidiagonalTuple]

/-- If the entry law `μ` is symmetric and `μ.MomentDominated s2` holds, a stage with `c` rows
satisfies the `t`-th moment bound with constant `s2 ^ t * chiSquareMoment c t`. -/
theorem MomentBound.stage (μ : EntryLaw) (hsymm : μ.Symmetric)
    {s2 : ℝ≥0} (hs : μ.MomentDominated s2)
    (c t : ℕ) : MomentBound (MultiStage.stage μ c : TableKernel f F c F)
      t ((s2 : ℝ≥0∞) ^ t * chiSquareMoment c t) := by
  exact stage_moment_le μ hsymm hs c t

/-- A deterministic map `g` that preserves the squared norm satisfies the `t`-th moment bound with
constant `1`. -/
theorem MomentBound.ofFun (g : Table f F → Table f' F')
    (hg : ∀ X, sqNorm (g X) = sqNorm X) (t : ℕ) :
    MomentBound (TableKernel.ofFun g) t 1 := by
  intro X
  simp [TableKernel.ofFun, expectation_pure, hg]

/-- If `K₁` and `K₂` satisfy the `t`-th moment bound with constants `M₁` and `M₂`, then
`K₁.andThen K₂` satisfies it with constant `M₁ * M₂`. -/
theorem MomentBound.andThen (h₁ : MomentBound K₁ t M₁) (h₂ : MomentBound K₂ t M₂) :
    MomentBound (K₁.andThen K₂) t (M₁ * M₂) := by
  intro X
  rw [TableKernel.andThen, expectation_bind]
  calc
    _ ≤ expectation (K₁ X) (fun Y => M₂ * (sqNorm Y : ℝ≥0∞) ^ t) :=
      expectation_mono _ (fun Y => h₂ Y)
    _ = M₂ * expectation (K₁ X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ t) :=
      expectation_const_mul _ _ _
    _ ≤ M₂ * (M₁ * (sqNorm X : ℝ≥0∞) ^ t) := mul_le_mul' le_rfl (h₁ X)
    _ = (M₁ * M₂) * (sqNorm X : ℝ≥0∞) ^ t := by ac_rfl

/-- If every branch `K i` satisfies the `k`-th moment bound with constant `m k` for every `k ≤ t`,
then `branches K` satisfies the `t`-th moment bound with constant `branchMoment g m t`. -/
theorem MomentBound.branches {K : Fin g → TableKernel f F c F'} {m : ℕ → ℝ≥0∞} {t : ℕ}
    (h : ∀ i k, k ≤ t → MomentBound (K i) k (m k)) :
    MomentBound (MultiStage.branches K) t (branchMoment g m t) := by
  classical
  intro X
  rw [MultiStage.branches, expectation_map]
  simp_rw [sqNorm_stack, Nat.cast_sum, sum_pow_antidiagonalTuple]
  rw [expectation_finset_sum]
  simp_rw [expectation_const_mul]
  have hind (k : Fin g → ℕ) :
      expectation (piPMF fun i => K i X) (fun Y => ∏ i, (sqNorm (Y i) : ℝ≥0∞) ^ k i) =
        ∏ i, expectation (K i X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ k i) :=
    expectation_piPMF_prod (fun i => K i X) (fun i Y => (sqNorm Y : ℝ≥0∞) ^ k i)
  simp_rw [hind]
  calc
    _ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple g t,
        (Nat.multinomial Finset.univ k : ℝ≥0∞) *
          ∏ i, (m (k i) * (sqNorm X : ℝ≥0∞) ^ k i) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul' le_rfl
      apply Finset.prod_le_prod'
      intro i _
      apply h i (k i) _ X
      rw [← Finset.Nat.mem_antidiagonalTuple.mp hk]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
    _ = branchMoment g m t * (sqNorm X : ℝ≥0∞) ^ t := by
      simp_rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [branchMoment, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.Nat.mem_antidiagonalTuple.mp hk, mul_assoc]

/-- Markov's inequality for the `t`-th moment: if `MomentBound K t M` holds, the probability that
the output `Y` of `K X` has `θ < sqNorm Y` is at most `M * sqNorm X ^ t / θ ^ t`. -/
theorem MomentBound.tail_le (h : MomentBound K t M) (X : Table f F) (θ : ℕ) :
    eventProbability (K X) (fun Y => θ < sqNorm Y) ≤ M * (sqNorm X : ℝ≥0∞) ^ t / (θ : ℝ≥0∞) ^ t :=
  by
    classical
    have hevent : eventProbability (K X) (fun Y => θ < sqNorm Y) =
        ∑' Y, if θ < sqNorm Y then K X Y else 0 := by
      simp [eventProbability, PMF.map_apply]
    have hmarkov : eventProbability (K X) (fun Y => θ < sqNorm Y) *
        ((θ + 1 : ℕ) : ℝ≥0∞) ^ t ≤
        expectation (K X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ t) := by
      rw [hevent, ← ENNReal.tsum_mul_right]
      apply ENNReal.tsum_le_tsum
      intro Y
      by_cases hY : θ < sqNorm Y
      · simp only [if_pos hY]
        apply mul_le_mul' le_rfl
        exact pow_le_pow_left' (by exact_mod_cast Nat.succ_le_of_lt hY) t
      · simp [hY]
    have hd0 : ((θ + 1 : ℕ) : ℝ≥0∞) ^ t ≠ 0 := by simp
    have hdt : ((θ + 1 : ℕ) : ℝ≥0∞) ^ t ≠ ∞ := by simp
    calc
      _ ≤ expectation (K X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ t) /
          ((θ + 1 : ℕ) : ℝ≥0∞) ^ t :=
        (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdt)).2 hmarkov
      _ ≤ M * (sqNorm X : ℝ≥0∞) ^ t / (θ : ℝ≥0∞) ^ t := by
        apply ENNReal.div_le_div (h X)
        exact pow_le_pow_left' (by exact_mod_cast Nat.le_succ θ) t

end CertifiedProjections.MultiStage
