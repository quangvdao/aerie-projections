/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Table

/-!
# Re-indexing a table by flat index

The entry in row `k` and column `φ` of a table with `f` rows has flat index `k + f * φ`. Two table
shapes with the same number of entries are identified by `flatEquiv`, the re-indexing that preserves
the flat index (`flatEquiv_val`).

Between two stages, the columns of the output are indexed by a low digit `x` and a high digit `φ`,
and the next stage takes the row `k` and the digit `x` together as its row index
`finProdFinEquiv (x, k)`, whose value is `k + c * x`. `flatEquiv_merge` and
`reshape_flatEquiv_merge` describe `flatEquiv` in this case, and `mul_reshape_flatEquiv` writes the
product of a matrix with the re-indexed table as a sum over `k` and `x`. `stack_apply` gives the
entries of a stack.
-/

open scoped BigOperators

namespace CertifiedProjections.MultiStage

variable {f F f' F' : ℕ}

/-- The re-indexing between the shapes `f × F` and `f' × F'` that preserves the flat index: the
entry in row `k` and column `φ` has flat index `k + f * φ` (see `flatEquiv_val`). -/
def flatEquiv (h : F * f = F' * f') : Fin f × Fin F ≃ Fin f' × Fin F' :=
  (((Equiv.prodComm _ _).trans finProdFinEquiv).trans (finCongr h)).trans
    (finProdFinEquiv.symm.trans (Equiv.prodComm _ _))

/-- `flatEquiv h` preserves the flat index. -/
theorem flatEquiv_val (h : F * f = F' * f') (x : Fin f × Fin F) :
    ((flatEquiv h x).1 : ℕ) + f' * (flatEquiv h x).2 = x.1 + f * x.2 := by
  simp only [flatEquiv, Equiv.trans_apply, Equiv.prodComm_apply, finProdFinEquiv_symm_apply]
  exact Nat.mod_add_div _ _

variable {c r m g : ℕ}

/-- `flatEquiv` moves the low digit `x` of the column index into the row index: the entry in row `k`
and column `finProdFinEquiv (φ, x)` (value `x + r * φ`) goes to row `finProdFinEquiv (x, k)` (value
`k + c * x`) and column `φ`. -/
theorem flatEquiv_merge (h : F * r * c = F * (r * c)) (k : Fin c) (x : Fin r) (φ : Fin F) :
    flatEquiv h (k, finProdFinEquiv (φ, x)) = (finProdFinEquiv (x, k), φ) := by
  apply ((Equiv.prodComm _ _).trans finProdFinEquiv).injective
  apply Fin.ext
  change ((flatEquiv h (k, finProdFinEquiv (φ, x))).1 : ℕ) +
    (r * c) * (flatEquiv h (k, finProdFinEquiv (φ, x))).2 = _
  rw [flatEquiv_val]
  change k.val + c * (finProdFinEquiv (φ, x)).val =
    (finProdFinEquiv (x, k)).val + (r * c) * φ.val
  simp only [finProdFinEquiv_apply_val]
  ring

/-- The entry of `reshape (flatEquiv h) Y` in row `finProdFinEquiv (x, k)` and column `φ` is the
entry of `Y` in row `k` and column `finProdFinEquiv (φ, x)`. -/
theorem reshape_flatEquiv_merge (h : F * r * c = F * (r * c)) (Y : Table c (F * r))
    (k : Fin c) (x : Fin r) (φ : Fin F) :
    reshape (flatEquiv h) Y (finProdFinEquiv (x, k)) φ = Y k (finProdFinEquiv (φ, x)) := by
  simp only [reshape, Matrix.of_apply]
  rw [← flatEquiv_merge h k x φ, Equiv.symm_apply_apply]

/-- A matrix `A` applied to the re-indexed table contracts the row `k` of `Y` together with the low
digit `x` of its column index: the column of `A` is `finProdFinEquiv (x, k)`, with value
`k + c * x`. Spec F §6.3. -/
theorem mul_reshape_flatEquiv (h : F * r * c = F * (r * c)) (A : Matrix (Fin m) (Fin (r * c)) ℤ)
    (Y : Table c (F * r)) (o : Fin m) (φ : Fin F) :
    (A * reshape (flatEquiv h) Y) o φ =
      ∑ k : Fin c, ∑ x : Fin r, A o (finProdFinEquiv (x, k)) * Y k (finProdFinEquiv (φ, x)) := by
  rw [Matrix.mul_apply, ← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, reshape_flatEquiv_merge]
  rw [Finset.sum_comm]

/-- Row `finProdFinEquiv (i, k)` (value `k + c * i`) of `stack T` is row `k` of `T i`. -/
theorem stack_apply (T : Fin g → Table c F) (i : Fin g) (k : Fin c) (φ : Fin F) :
    stack T (finProdFinEquiv (i, k)) φ = T i k φ := by
  simp only [stack, Matrix.of_apply, Equiv.symm_apply_apply]

end CertifiedProjections.MultiStage
