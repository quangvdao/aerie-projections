/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.EntryLaw
import CertifiedProjections.MultiStage.Table

/-!
# Stages and table kernels

A table kernel (`TableKernel`) maps each input table to a law on output tables. A stage (`stage`)
draws a matrix `C` with independent entries from an entry law and outputs `C * X`, and `stageMod`
centers that output modulo `p`. Larger kernels are built from stages and deterministic steps
(`TableKernel.ofFun`) by sequential composition (`TableKernel.andThen`). The predicate
`ModOf p Kmod K` says that `Kmod` is the kernel `K` computed modulo `p`. It holds for stages, for
deterministic steps that commute with centering, and for compositions (spec H1).
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}
variable {f₁ F₁ f₂ F₂ p : ℕ} {μ : EntryLaw}

/-- A table kernel: a map sending each input table to a law on output tables. A multi-stage
projection is a `TableKernel`. -/
abbrev TableKernel (f F f' F' : ℕ) := Table f F → PMF (Table f' F')

namespace TableKernel
/-- The deterministic table kernel that outputs `g X` on input `X`. -/
noncomputable def ofFun (g : Table f F → Table f' F') : TableKernel f F f' F' :=
  fun X => PMF.pure (g X)
/-- Sequential composition: run `K₁` on the input, then `K₂` on the output of `K₁`. -/
noncomputable def andThen (K₁ : TableKernel f F f₁ F₁) (K₂ : TableKernel f₁ F₁ f₂ F₂) :
    TableKernel f F f₂ F₂ := fun X => (K₁ X).bind K₂
end TableKernel

/-- One stage over ℤ: draw a matrix `C` with `c` rows and independent entries from `μ`, and output
`C * X`. -/
noncomputable def stage (μ : EntryLaw) (c : ℕ) : TableKernel f F c F :=
  fun X => (μ.matrixPMF c f).map fun C => Matrix.of C * X
/-- One stage modulo `p`: the output of `stage μ c`, centered modulo `p`. -/
noncomputable def stageMod (p : ℕ) (μ : EntryLaw) (c : ℕ) : TableKernel f F c F :=
  fun X => (stage μ c X).map (ctr p)

/-- `Kmod` is the integer kernel `K` computed modulo `p`: for every table `X`, running `Kmod` on
`ctr p X` gives the same law as running `K` on `X` and centering the output modulo `p`. -/
def ModOf (p : ℕ) (Kmod K : TableKernel f F f' F') : Prop :=
  ∀ X, Kmod (ctr p X) = (K X).map (ctr p)

variable {X X' : Table f F}
variable {Kmod₁ K₁ : TableKernel f F f₁ F₁} {Kmod₂ K₂ : TableKernel f₁ F₁ f₂ F₂}

/-- Centering `X` before multiplying by `C` does not change the centered product:
`ctr p (C * ctr p X) = ctr p (C * X)`. -/
private theorem ctr_mul_ctr (C : Table c f) (X : Table f F) :
    ctr p (C * ctr p X) = ctr p (C * X) := by
  ext i j
  change centeredMod p (∑ k, C i k * centeredMod p (X k j)) =
    centeredMod p (∑ k, C i k * X k j)
  unfold centeredMod
  congr 1
  simp only [Int.cast_sum, Int.cast_mul, ZMod.coe_valMinAbs]

/-- If `X` and `X'` have the same centering modulo `p`, then `stageMod p μ c` has the same output
law on `X` and on `X'`. -/
theorem stageMod_congr (h : ctr p X = ctr p X') : stageMod p μ c X = stageMod p μ c X' := by
  unfold stageMod stage
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext C
  change ctr p (Matrix.of C * X) = ctr p (Matrix.of C * X')
  rw [← ctr_mul_ctr, h, ctr_mul_ctr]
/-- `stageMod p μ c` is `stage μ c` computed modulo `p`. -/
theorem ModOf.stage : ModOf p (stageMod p μ c : TableKernel f F c F) (MultiStage.stage μ c) :=
  by
    intro X
    exact stageMod_congr ctr_ctr
/-- If the deterministic map `g` commutes with centering modulo `p`, then `ofFun g` is `ofFun g`
computed modulo `p`. -/
theorem ModOf.ofFun (g : Table f F → Table f' F') (hg : ∀ X, g (ctr p X) = ctr p (g X)) :
    ModOf p (TableKernel.ofFun g) (TableKernel.ofFun g) := by
  intro X
  simpa only [TableKernel.ofFun, PMF.pure_map] using congrArg PMF.pure (hg X)
/-- If `Kmod₁` and `Kmod₂` are `K₁` and `K₂` computed modulo `p`, then `Kmod₁.andThen Kmod₂` is
`K₁.andThen K₂` computed modulo `p`. -/
theorem ModOf.andThen (h₁ : ModOf p Kmod₁ K₁) (h₂ : ModOf p Kmod₂ K₂) :
    ModOf p (Kmod₁.andThen Kmod₂) (K₁.andThen K₂) := by
  intro X
  unfold TableKernel.andThen
  rw [h₁ X, PMF.bind_map, PMF.map_bind]
  congr 1
  funext Y
  exact h₂ Y

end CertifiedProjections.MultiStage
