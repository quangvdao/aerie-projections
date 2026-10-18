/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Distributions.SparseRademacher
import CertifiedProjections.Model.ProjectionDistribution
import CertifiedProjections.Probability.Finite.UniformPiBridge
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Exact entry, row, and matrix laws

This module specializes the uniform finite-function bridge to the balanced-
ternary experiment used by CertifiedProjections. It records the exact entry masses,
coordinate marginals, product-measure identities, and row and whole-matrix
entry independence.
-/

open scoped ENNReal
open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections

/--
The sparse-row PMF is a coordinatewise image of independent uniform bit pairs.
-/
theorem sparseRademacherRow_eq_uniformPiMap (d : ℕ) :
    sparseRademacherRow d =
      uniformPiMap (fun _ : Fin d => sparseBit) := by
  rfl

/-- A sparse row is also the image of one uniform sparse-row seed. -/
theorem sparseRademacherRow_eq_map_uniformRowSeed (d : ℕ) :
    sparseRademacherRow d =
      (PMF.uniformOfFintype (SparseRowSeed d)).map sparseRow := by
  unfold sparseRademacherRow uniformPiMap
  rw [uniformPiPMF_eq_uniformOfFintype]
  rfl

/-- A sparse matrix is the image of one uniform sparse-matrix seed. -/
theorem sparseRademacherMatrix_eq_map_uniformSeed (m d : ℕ) :
    sparseRademacherMatrix m d =
      (PMF.uniformOfFintype (SparseSeed m d)).map sparseMatrix := by
  unfold sparseRademacherMatrix uniformPiMap
  rw [uniformPiPMF_eq_uniformOfFintype]
  rfl

/--
The sparse-matrix PMF is a product of identically distributed sparse rows.
-/
theorem sparseRademacherMatrix_eq_uniformPiMap (m d : ℕ) :
    sparseRademacherMatrix m d =
      uniformPiMap (fun _ : Fin m => @sparseRow d) := by
  rfl

/-- A sparse matrix has the product measure of its sparse-row marginals. -/
theorem sparseRademacherMatrix_toMeasure (m d : ℕ) :
    (sparseRademacherMatrix m d).toMeasure =
      Measure.pi (fun _ : Fin m => (sparseRademacherRow d).toMeasure) := by
  rw [sparseRademacherMatrix_eq_uniformPiMap]
  simpa [sparseRademacherRow_eq_map_uniformRowSeed] using
    (uniformPiMap_toMeasure
      (f := fun _ : Fin m => @sparseRow d)
      (fun _ => measurable_of_finite sparseRow))

/-- A sparse entry equals `-1` with probability `1/4`. -/
@[simp]
theorem sparseEntryPMF_neg_one :
    sparseEntryPMF (-1) = (4 : ℝ≥0∞)⁻¹ := by
  simp only [sparseEntryPMF, PMF.map_apply,
    PMF.uniformOfFintype_apply, tsum_fintype,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [sparseBit, Fintype.card_prod, Fintype.card_bool,
    Nat.reduceMul, Nat.cast_ofNat, reduceIte]
  norm_num

/-- A sparse entry equals `0` with probability `1/2`. -/
@[simp]
theorem sparseEntryPMF_zero :
    sparseEntryPMF 0 = (2 : ℝ≥0∞)⁻¹ := by
  simp only [sparseEntryPMF, PMF.map_apply,
    PMF.uniformOfFintype_apply, tsum_fintype,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [sparseBit, Fintype.card_prod, Fintype.card_bool,
    Nat.reduceMul, Nat.cast_ofNat, reduceIte]
  norm_num
  calc
    (4 : ℝ≥0∞)⁻¹ + 4⁻¹ =
        (2⁻¹ * 2⁻¹) + (2⁻¹ * 2⁻¹) := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
      rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
    _ = (2⁻¹ + 2⁻¹) * 2⁻¹ := by rw [add_mul]
    _ = 2⁻¹ := by rw [ENNReal.inv_two_add_inv_two, one_mul]

/-- A sparse entry equals `1` with probability `1/4`. -/
@[simp]
theorem sparseEntryPMF_one :
    sparseEntryPMF 1 = (4 : ℝ≥0∞)⁻¹ := by
  simp only [sparseEntryPMF, PMF.map_apply,
    PMF.uniformOfFintype_apply, tsum_fintype,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [sparseBit, Fintype.card_prod, Fintype.card_bool,
    Nat.reduceMul, Nat.cast_ofNat, reduceIte]
  norm_num

/-- A sparse entry has no mass away from `{-1, 0, 1}`. -/
theorem sparseEntryPMF_eq_zero {z : ℤ}
    (hzNeg : z ≠ -1) (hzZero : z ≠ 0) (hzPos : z ≠ 1) :
    sparseEntryPMF z = 0 := by
  simp [sparseEntryPMF, PMF.map_apply, sparseBit,
    PMF.uniformOfFintype_apply, hzNeg, hzZero, hzPos]

/-- A sparse-ternary entry is centered under its exact finite PMF. -/
theorem sparseEntry_firstMoment :
    ∫ z, (z : ℝ) ∂sparseEntryPMF.toMeasure = 0 := by
  rw [sparseEntryPMF]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (Bool × Bool)) (f := sparseBit)
    (measurable_of_finite sparseBit)]
  rw [integral_map_of_stronglyMeasurable
    (measurable_of_finite sparseBit)
    (measurable_of_countable
      (fun z : ℤ => (z : ℝ))).stronglyMeasurable]
  rw [finitePMF_integral_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, sparseBit]

/-- A sparse-ternary entry has exact variance `1/2`. -/
theorem sparseEntry_secondMoment :
    ∫ z, (z : ℝ) ^ 2 ∂sparseEntryPMF.toMeasure = (1 / 2 : ℝ) := by
  rw [sparseEntryPMF]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (Bool × Bool)) (f := sparseBit)
    (measurable_of_finite sparseBit)]
  rw [integral_map_of_stronglyMeasurable
    (measurable_of_finite sparseBit)
    (measurable_of_countable
      (fun z : ℤ => (z : ℝ) ^ 2)).stronglyMeasurable]
  rw [finitePMF_integral_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [PMF.uniformOfFintype_apply, sparseBit]
  norm_num

/-- A sparse row has the product measure of its sparse-entry marginals. -/
theorem sparseRademacherRow_toMeasure (d : ℕ) :
    (sparseRademacherRow d).toMeasure =
      Measure.pi (fun _ : Fin d => sparseEntryPMF.toMeasure) := by
  rw [sparseRademacherRow_eq_uniformPiMap]
  simpa [sparseEntryPMF] using
    (uniformPiMap_toMeasure
      (f := fun _ : Fin d => sparseBit)
      (fun _ => measurable_of_finite sparseBit))

/-- Every coordinate of a sparse row has the exact sparse-entry marginal. -/
theorem sparseRademacherRow_marginal {d : ℕ} (i : Fin d) :
    (sparseRademacherRow d).map (fun row => row i) = sparseEntryPMF := by
  rw [sparseRademacherRow_eq_uniformPiMap]
  simpa [sparseEntryPMF] using
    (uniformPiMap_marginal
      (f := fun _ : Fin d => sparseBit) i)

/-- The entries of a sparse row are mutually independent. -/
theorem sparseRademacherRow_iIndepEntries (d : ℕ) :
    iIndepFun (fun i row => row i) (sparseRademacherRow d).toMeasure := by
  rw [sparseRademacherRow_eq_uniformPiMap]
  exact uniformPiMap_iIndep
    (f := fun _ : Fin d => sparseBit)
    (fun _ => measurable_of_finite sparseBit)

/-- The rows of a sparse matrix are mutually independent. -/
theorem sparseRademacherMatrix_iIndepRows (m d : ℕ) :
    iIndepFun (fun j J => J j) (sparseRademacherMatrix m d).toMeasure := by
  rw [sparseRademacherMatrix_eq_uniformPiMap]
  exact uniformPiMap_iIndep
    (f := fun _ : Fin m => @sparseRow d)
    (fun _ => measurable_of_finite sparseRow)

/-- Every row of a sparse matrix has the exact sparse-row marginal. -/
theorem sparseRademacherMatrix_rowMarginal {m d : ℕ} (j : Fin m) :
    (sparseRademacherMatrix m d).map (fun J => J j) = sparseRademacherRow d := by
  rw [sparseRademacherMatrix_eq_uniformPiMap]
  calc
    (uniformPiMap (fun _ : Fin m => @sparseRow d)).map
        (fun J => J j) =
        (PMF.uniformOfFintype (SparseRowSeed d)).map sparseRow := by
      simpa using
        (uniformPiMap_marginal
          (f := fun _ : Fin m => @sparseRow d) j)
    _ = sparseRademacherRow d := (sparseRademacherRow_eq_map_uniformRowSeed d).symm

namespace ProjectionDistribution

/-- Every row of a matrix sampled from a supported projection distribution has
the corresponding one-row marginal. -/
theorem matrixPMF_rowMarginal
    (distribution : ProjectionDistribution) (rows d : ℕ) (j : Fin rows) :
    (distribution.matrixPMF rows d).map (fun J => J j) =
      distribution.rowPMF d := by
  cases distribution
  exact sparseRademacherMatrix_rowMarginal j

end ProjectionDistribution

/-- Every sparse-matrix entry has the exact sparse-entry marginal. -/
theorem sparseRademacherMatrix_entryMarginal {m d : ℕ} (j : Fin m) (i : Fin d) :
    (sparseRademacherMatrix m d).map (fun J => J j i) = sparseEntryPMF := by
  calc
    (sparseRademacherMatrix m d).map (fun J => J j i) =
        ((sparseRademacherMatrix m d).map (fun J => J j)).map
          (fun row => row i) := by
      rw [PMF.map_comp]
      rfl
    _ = (sparseRademacherRow d).map (fun row => row i) := by
      rw [sparseRademacherMatrix_rowMarginal j]
    _ = sparseEntryPMF := sparseRademacherRow_marginal i

private theorem iIndepFun_comp_of_map_eq
    {ι Ω Ω' : Type*} [Finite ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ]
    (f : Ω → Ω') (g : (i : ι) → Ω' → β i)
    (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (hmap : μ.map f = ν) (hindep : iIndepFun g ν) :
    iIndepFun (fun i => g i ∘ f) μ := by
  let := Fintype.ofFinite ι
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hg i).comp hf).aemeasurable)]
  calc
    μ.map (fun ω i => g i (f ω)) =
        (μ.map f).map (fun x i => g i x) := by
      rw [Measure.map_map (measurable_pi_iff.mpr hg) hf]
      rfl
    _ = ν.map (fun x i => g i x) := by rw [hmap]
    _ = Measure.pi (fun i => ν.map (g i)) :=
      hindep.map_fun_eq_pi_map (fun i => (hg i).aemeasurable)
    _ = Measure.pi (fun i => μ.map (fun ω => g i (f ω))) := by
      congr 1
      funext i
      rw [← hmap, Measure.map_map (hg i) hf]
      rfl

/-- All entries of a sparse matrix are mutually independent. -/
theorem sparseRademacherMatrix_iIndepEntries (m d : ℕ) :
    iIndepFun (fun p : Fin m × Fin d => fun J => J p.1 p.2)
      (sparseRademacherMatrix m d).toMeasure := by
  apply iIndepFun_uncurry' (by fun_prop)
    (sparseRademacherMatrix_iIndepRows m d)
  intro j
  have hmap :
      (sparseRademacherMatrix m d).toMeasure.map (fun J => J j) =
        (sparseRademacherRow d).toMeasure := by
    calc
      (sparseRademacherMatrix m d).toMeasure.map (fun J => J j) =
          ((sparseRademacherMatrix m d).map (fun J => J j)).toMeasure :=
        PMF.toMeasure_map
          (p := sparseRademacherMatrix m d) (f := fun J => J j) (by fun_prop)
      _ = (sparseRademacherRow d).toMeasure := by
        rw [sparseRademacherMatrix_rowMarginal j]
  simpa [Function.comp_def] using
    (iIndepFun_comp_of_map_eq
      (μ := (sparseRademacherMatrix m d).toMeasure)
      (ν := (sparseRademacherRow d).toMeasure)
      (f := fun J => J j) (g := fun i row => row i)
      (by fun_prop) (by fun_prop) hmap
      (sparseRademacherRow_iIndepEntries d))

end CertifiedProjections
