/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Stage

/-!
# Independent branches

`piPMF P` is the law of a tuple with independent coordinates, the `i`-th drawn from `P i`.
`branches K` runs the table kernels `K i` independently on the same input and stacks their outputs
(spec H1). The predicate `ModOf` is preserved by `branches` (`ModOf.branches`).
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}
variable {β : Type*}

/-- The law of a tuple `y : Fin g → β` with independent coordinates, where `y i` is drawn from
`P i`. Defined by recursion on `g`. -/
noncomputable def piPMF {β : Type*} : {g : ℕ} → (Fin g → PMF β) → PMF (Fin g → β)
  | 0, _ => PMF.pure Fin.elim0
  | n + 1, P => (P 0).bind fun a => (piPMF (fun i : Fin n => P i.succ)).map (Fin.cons a)
/-- The mass of `y` under `piPMF P` is the product over `i` of the mass of `y i` under `P i`. -/
theorem piPMF_apply (P : Fin g → PMF β) (y : Fin g → β) : piPMF P y = ∏ i, P i (y i) := by
  classical
  induction g with
  | zero =>
      have hy : y = Fin.elim0 := Subsingleton.elim _ _
      simp [piPMF, hy]
  | succ n ih =>
      rw [piPMF, PMF.bind_apply, Fin.prod_univ_succ]
      simp only [PMF.map_apply]
      conv_lhs => rw [← Fin.cons_self_tail y]
      simp only [Fin.cons_inj]
      simp only [ite_and, ih]
      rw [tsum_eq_single (y 0)]
      · simp [Fin.tail]
      · intro a ha
        simp [Ne.symm ha]
/-- Applying `f` to every coordinate of a draw from `piPMF Q` gives a draw from `piPMF` of the laws
`(Q i).map f`. -/
theorem piPMF_map {α β : Type*} {n : ℕ} (Q : Fin n → PMF α) (f : α → β) :
    (piPMF Q).map (fun x i => f (x i)) = piPMF (fun i => (Q i).map f) := by
  induction n with
  | zero =>
      simp only [piPMF, PMF.pure_map]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [piPMF, PMF.map_bind, PMF.bind_map, Function.comp_def]
      congr 1
      funext a
      rw [← ih, PMF.map_comp, PMF.map_comp]
      congr 1
      funext x
      funext i
      cases i using Fin.cases <;> rfl

/-- Every coordinate of a point in the support of `piPMF Q` is in the support of its own law. -/
theorem mem_support_of_mem_support_piPMF {α : Type*} {n : ℕ} (Q : Fin n → PMF α)
    {x : Fin n → α} (hx : x ∈ (piPMF Q).support) (i : Fin n) : x i ∈ (Q i).support := by
  rw [PMF.mem_support_iff, piPMF_apply] at hx
  rw [PMF.mem_support_iff]
  exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)

/-- For independent coordinates, the expectation of a product of functions of the single coordinates
is the product of their expectations. -/
theorem expectation_piPMF_prod {β : Type*} {n : ℕ} (P : Fin n → PMF β)
    (u : Fin n → β → ℝ≥0∞) :
    expectation (piPMF P) (fun y => ∏ i, u i (y i)) =
      ∏ i, expectation (P i) (u i) := by
  induction n with
  | zero => simp [piPMF, expectation_pure]
  | succ n ih =>
    rw [piPMF, expectation_bind]
    simp_rw [expectation_map, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      expectation_const_mul, ih]
    unfold expectation
    simp_rw [← mul_assoc, ENNReal.tsum_mul_right]

/-- Independent branches: run every `K i` on the same input `X`, independently, and stack the
outputs. -/
noncomputable def branches (K : Fin g → TableKernel f F c F') : TableKernel f F (g * c) F' :=
  fun X => (piPMF fun i => K i X).map stack

variable {p : ℕ} {Kmod K : Fin g → TableKernel f F c F'}

/-- If every `Kmod i` is `K i` computed modulo `p`, then `branches Kmod` is `branches K` computed
modulo `p`. -/
theorem ModOf.branches (h : ∀ i, ModOf p (Kmod i) (K i)) :
    ModOf p (MultiStage.branches Kmod) (MultiStage.branches K) :=
  by
    intro X
    unfold MultiStage.branches
    simp_rw [h _ X]
    rw [(piPMF_map _ _).symm, PMF.map_comp, PMF.map_comp]
    congr 1

end CertifiedProjections.MultiStage
