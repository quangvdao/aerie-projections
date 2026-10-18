/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Stage
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-!
# MGF bound for one stage

This file bounds the moment generating function (MGF) of the squared norm of a stage output,
relative to the squared norm of the input. The main result is `stage_mgf_le`: if the entry law `μ`
satisfies `μ.MGFConstant t K`, then for every nonzero table `X` the expectation of
`exp (-t * sqNorm Y / sqNorm X)` over the output `Y` of a stage with `c` rows is at most `K ^ c`.

Spec Lemma C.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}

/-- Under the uniform law on `Fin c → α`, the expectation of `∏ i, g (a i)` is the `c`-th power of
the expectation of `g` under the uniform law on `α`. -/
private theorem expectation_uniform_prod {α : Type*} [Fintype α] [Nonempty α]
    (c : ℕ) (g : α → ℝ≥0∞) :
    expectation (PMF.uniformOfFintype (Fin c → α)) (fun a => ∏ i, g (a i)) =
      expectation (PMF.uniformOfFintype α) g ^ c := by
  classical
  simp only [expectation, tsum_fintype, PMF.uniformOfFintype_apply]
  simp only [← Finset.mul_sum, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    ENNReal.inv_pow]
  rw [mul_pow, Fintype.sum_pow]

/-- For a constant family of types, `uniformPiPMF` is the uniform law on the function type
`ι → α`. -/
private theorem uniformPiPMF_const {ι α : Type*} [DecidableEq ι] [Fintype ι] [Fintype α]
    [Nonempty α] : uniformPiPMF (fun _ : ι => α) = PMF.uniformOfFintype (ι → α) := by
  unfold uniformPiPMF
  congr 1
  exact Subsingleton.elim _ _

/-- The expectation of `g` under `μ.rowPMF f` is the expectation, over a uniform vector `s` of `f`
seeds, of `g` applied to the row of values `μ.value (s i)`. -/
private theorem expectation_row (μ : EntryLaw) (f : ℕ) (g : (Fin f → ℤ) → ℝ≥0∞) :
    expectation (μ.rowPMF f) g =
      expectation (PMF.uniformOfFintype (Fin f → μ.Seed))
        (fun s => g (fun i => μ.value (s i))) := by
  unfold EntryLaw.rowPMF uniformPiMap
  rw [expectation_map]
  rw [uniformPiPMF_const]

/-- Under `μ.matrixPMF c f`, the expectation of the product over the `c` rows `a i` of `g (a i)` is
the `c`-th power of the expectation of `g` under `μ.rowPMF f`. -/
private theorem expectation_matrix_prod (μ : EntryLaw) (c f : ℕ)
    (g : (Fin f → ℤ) → ℝ≥0∞) :
    expectation (μ.matrixPMF c f) (fun a => ∏ i, g (a i)) =
      expectation (μ.rowPMF f) g ^ c := by
  rw [EntryLaw.matrixPMF, uniformPiMap, expectation_map, expectation_row, uniformPiPMF_const]
  change expectation (PMF.uniformOfFintype (Fin c → Fin f → μ.Seed))
    (fun a => ∏ i, g (fun j => μ.value (a i j))) = _
  exact expectation_uniform_prod c (fun a : Fin f → μ.Seed => g (fun j => μ.value (a j)))

/-- The squared norm of `Matrix.of C * X`, as a real number, is the sum over rows `i` of `C` and
columns `j` of `X` of the squared dot product of row `i` of `C` with column `j` of `X`. -/
private theorem sqNorm_mul_cast (C : Fin c → Fin f → ℤ) (X : Table f F) :
    (sqNorm (Matrix.of C * X) : ℝ) =
      ∑ i, ∑ j, realRowDot (C i) (fun k => (X k j : ℝ)) ^ 2 := by
  rw [sqNorm_cast_real]
  simp [Matrix.mul_apply, realRowDot]

/-- Jensen's inequality for `Real.exp` with weights `n j / D`: if the `n j` are nonnegative and sum
to `D > 0`, and `d j = 0` whenever `n j = 0`, then `exp (-t * (∑ j, d j) / D)` is at most
`∑ j, (n j / D) * exp (-t * d j / n j)`. -/
private theorem weighted_exp_le (n d : Fin F → ℝ) (D t : ℝ)
    (hn : ∀ j, 0 ≤ n j) (hD : 0 < D) (hSum : ∑ j, n j = D)
    (hz : ∀ j, n j = 0 → d j = 0) :
    Real.exp (-t * (∑ j, d j) / D) ≤
      ∑ j, (n j / D) * Real.exp (-t * d j / n j) := by
  have hw : ∑ j, n j / D = 1 := by
    rw [← Finset.sum_div, hSum, div_self hD.ne']
  have harg : (∑ j, (n j / D) * (-t * d j / n j)) =
      -t * (∑ j, d j) / D := by
    calc
      _ = ∑ j, -t * d j / D := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : n j = 0
        · simp [hj, hz j hj]
        · field_simp
      _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]
  have hJ := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := fun j : Fin F => n j / D)
    (p := fun j => -t * d j / n j)
    (fun j _ => div_nonneg (hn j) hD.le) hw (fun j _ => Set.mem_univ _)
  simpa only [smul_eq_mul, harg] using hJ

/-- If `μ.MGFConstant t K` holds and the real vector `v` is nonzero, then the expectation over a row
`a` drawn from `μ.rowPMF f` of `exp (-t * realRowDot a v ^ 2 / ∑ i, v i ^ 2)` is at most `K`. -/
private theorem row_column_mgf (μ : EntryLaw) {t K : ℝ} (hK : μ.MGFConstant t K)
    (v : Fin f → ℝ) (hn : 0 < ∑ i, v i ^ 2) :
    expectation (μ.rowPMF f)
      (fun a => ENNReal.ofReal (Real.exp (-t * realRowDot a v ^ 2 / (∑ i, v i ^ 2)))) ≤
      ENNReal.ofReal K := by
  let N := ∑ i, v i ^ 2
  have hsqrt : Real.sqrt N ^ 2 = N := Real.sq_sqrt hn.le
  have hu : (∑ i, (v i / Real.sqrt N) ^ 2) = 1 := by
    simp only [div_pow, ← Finset.sum_div]
    rw [hsqrt, div_self hn.ne']
  have hdot (a : Fin f → ℤ) :
      realRowDot a (fun i => v i / Real.sqrt N) ^ 2 = realRowDot a v ^ 2 / N := by
    simp only [realRowDot, ← mul_div_assoc, ← Finset.sum_div, div_pow, hsqrt]
  simpa only [hdot, mul_div_assoc] using hK f (fun i => v i / Real.sqrt N) hu

/-- If `μ.MGFConstant t K` holds and the table `X` is nonzero, then the expectation over a row `a`
drawn from `μ.rowPMF f` of `exp (-t * s / sqNorm X)` is at most `K`, where `s` is the sum over the
columns of `X` of the squared dot product of `a` with that column. -/
private theorem row_table_mgf (μ : EntryLaw) {t K : ℝ} (hK : μ.MGFConstant t K)
    (X : Table f F) (hX : X ≠ 0) :
    expectation (μ.rowPMF f) (fun a => ENNReal.ofReal
      (Real.exp (-t * (∑ j, realRowDot a (fun i => (X i j : ℝ)) ^ 2) /
        (sqNorm X : ℝ)))) ≤ ENNReal.ofReal K := by
  classical
  let n : Fin F → ℝ := fun j => ∑ i, (X i j : ℝ) ^ 2
  let D : ℝ := sqNorm X
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (Nat.pos_of_ne_zero (fun h => hX (sqNorm_eq_zero_iff.mp h)))
  have hn (j) : 0 ≤ n j := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsum : ∑ j, n j = D := by
    dsimp [n, D]
    rw [sqNorm_cast_real, Finset.sum_comm]
  have hz (j) (hj : n j = 0) : ∀ i, (X i j : ℝ) = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (X i j : ℝ))).mp hj
    intro i
    exact sq_eq_zero_iff.mp (hh i (Finset.mem_univ i))
  have hw (j) : 0 ≤ n j / D := div_nonneg (hn j) hD.le
  -- Jensen combines the columns with their normalized squared norms as weights.
  have hpoint (a : Fin f → ℤ) :
      ENNReal.ofReal (Real.exp (-t * (∑ j, realRowDot a (fun i => (X i j : ℝ)) ^ 2) / D)) ≤
        ∑ j, ENNReal.ofReal (n j / D) * ENNReal.ofReal
          (Real.exp (-t * realRowDot a (fun i => (X i j : ℝ)) ^ 2 / n j)) := by
    have hh := weighted_exp_le n (fun j => realRowDot a (fun i => (X i j : ℝ)) ^ 2)
      D t hn hD hsum (fun j hj => by simp [realRowDot, hz j hj])
    convert ENNReal.ofReal_le_ofReal hh using 1
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)]
    apply Finset.sum_congr rfl
    intro j _
    exact (ENNReal.ofReal_mul (hw j)).symm
  calc
    _ ≤ expectation (μ.rowPMF f) (fun a => ∑ j, ENNReal.ofReal (n j / D) *
        ENNReal.ofReal (Real.exp (-t * realRowDot a (fun i => (X i j : ℝ)) ^ 2 / n j))) := by
      exact ENNReal.tsum_le_tsum (fun a => mul_le_mul' le_rfl (hpoint a))
    _ = ∑ j, ENNReal.ofReal (n j / D) * expectation (μ.rowPMF f)
        (fun a => ENNReal.ofReal
          (Real.exp (-t * realRowDot a (fun i => (X i j : ℝ)) ^ 2 / n j))) := by
      rw [expectation_finset_sum (s := Finset.univ)]
      simp only [expectation_const_mul]
    _ ≤ ∑ j, ENNReal.ofReal (n j / D) * ENNReal.ofReal K := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : n j = 0
      · simp [hj]
      · exact mul_le_mul' le_rfl (row_column_mgf μ hK (fun i => (X i j : ℝ))
          (lt_of_le_of_ne (hn j) (Ne.symm hj)))
    _ = ENNReal.ofReal K := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hw j),
        ← Finset.sum_div, hsum, div_self hD.ne']
      simp

/-- If `μ.MGFConstant t K` holds and the table `X` is nonzero, then the expectation of
`exp (-t * sqNorm Y / sqNorm X)` over the output `Y` of `stage μ c X` is at most `K ^ c`. Spec Lemma
C. -/
theorem stage_mgf_le (μ : EntryLaw) {t K : ℝ} (hK : μ.MGFConstant t K)
    (c : ℕ) (X : Table f F) (hX : X ≠ 0) :
    expectation (stage μ c X)
        (fun Y => ENNReal.ofReal (Real.exp (-t * (sqNorm Y : ℝ) / (sqNorm X : ℝ)))) ≤
      ENNReal.ofReal K ^ c := by
  classical
  rw [stage, expectation_map]
  have hexp (C : Fin c → Fin f → ℤ) :
      ENNReal.ofReal (Real.exp (-t * (sqNorm (Matrix.of C * X) : ℝ) / (sqNorm X : ℝ))) =
        ∏ i, ENNReal.ofReal (Real.exp
          (-t * (∑ j, realRowDot (C i) (fun k => (X k j : ℝ)) ^ 2) / (sqNorm X : ℝ))) := by
    rw [sqNorm_mul_cast, Finset.mul_sum, Finset.sum_div, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  -- The exponential factors across the independently sampled rows.
  simp_rw [hexp]
  rw [expectation_matrix_prod μ c f (fun a => ENNReal.ofReal (Real.exp
    (-t * (∑ j, realRowDot a (fun k => (X k j : ℝ)) ^ 2) / (sqNorm X : ℝ))))]
  exact pow_le_pow_left₀ zero_le (row_table_mgf μ hK X hX) c

end CertifiedProjections.MultiStage
