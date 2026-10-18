/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Generic integer Gaussian tails

This module owns only the arithmetic and ENNReal series estimates used by
periodization and scalar-lobe arguments.  It deliberately has no sparse-row,
PMF, moment-law, or matrix imports, so changes to those models do not
invalidate scalar series consumers.
-/

open scoped BigOperators ENNReal

namespace CertifiedProjections

/-!
For `0 < ρ < 1`, the quadratic-exponent tail is bounded by a geometric
series with ratio `ρ³`.  The inequality `n² ≥ 1 + 3(n-1)` is the exact
integer estimate used in the paper's (L3).
-/
theorem gaussianImage_geometricTail
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt_one : ρ < 1) :
    ∑' n : ℕ, ρ ^ ((n + 1) ^ 2) ≤ ρ / (1 - ρ ^ 3) := by
  have hρ_nonneg : 0 ≤ ρ := hρ_pos.le
  have hρ_cube : ρ ^ 3 < 1 := by
    simpa using
      (pow_lt_pow_left₀ hρ_lt_one hρ_nonneg
        (by norm_num : (3 : ℕ) ≠ 0))
  have hbound (n : ℕ) :
      ρ ^ ((n + 1) ^ 2) ≤ ρ ^ (1 + 3 * n) := by
    apply pow_le_pow_of_le_one hρ_nonneg hρ_lt_one.le
    cases n with
    | zero => norm_num
    | succ n =>
        nlinarith [Nat.zero_le n]
  have hgeom :
      (∑' n : ℕ, ρ ^ (1 + 3 * n)) = ρ / (1 - ρ ^ 3) := by
    calc
      (∑' n : ℕ, ρ ^ (1 + 3 * n)) =
          ∑' n : ℕ, ρ * (ρ ^ 3) ^ n := by
        apply tsum_congr
        intro n
        calc
          ρ ^ (1 + 3 * n) = ρ ^ 1 * ρ ^ (3 * n) := by
            rw [pow_add]
          _ = ρ * (ρ ^ 3) ^ n := by
            rw [pow_mul]
            simp
      _ = ρ * ∑' n : ℕ, (ρ ^ 3) ^ n := by
        rw [tsum_mul_left]
      _ = ρ * (1 - ρ ^ 3)⁻¹ := by
        rw [tsum_geometric_of_lt_one (r := ρ ^ 3)
          (by positivity) hρ_cube]
      _ = ρ / (1 - ρ ^ 3) := by
        rfl
  calc
    ∑' n : ℕ, ρ ^ ((n + 1) ^ 2) ≤
        ∑' n : ℕ, ρ ^ (1 + 3 * n) := by
      have hsum_rhs : Summable (fun n : ℕ => ρ ^ (1 + 3 * n)) := by
        have hbase : Summable (fun n : ℕ => (ρ ^ 3) ^ n) :=
          summable_geometric_of_lt_one (by positivity) hρ_cube
        have hmul : Summable (fun n : ℕ => ρ * (ρ ^ 3) ^ n) :=
          hbase.mul_left ρ
        simpa [pow_add, pow_mul] using hmul
      have hsum_lhs : Summable (fun n : ℕ => ρ ^ ((n + 1) ^ 2)) :=
        hsum_rhs.of_nonneg_of_le (fun n => by positivity) hbound
      exact hsum_lhs.tsum_le_tsum hbound hsum_rhs
    _ = ρ / (1 - ρ ^ 3) := hgeom

/-!
The two-sided integer image series has the same geometric envelope.  This is
kept separate so a later scalar consumer can retain the full `ℤ` sum until
the explicit zero/nonzero split.
-/
theorem integerGaussian_geometricTail
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt_one : ρ < 1) :
    ∑' n : ℤ, ENNReal.ofReal (ρ ^ (Int.natAbs n) ^ 2) ≤
      ENNReal.ofReal (1 + 2 * ρ / (1 - ρ ^ 3)) := by
  let f : ℤ → ℝ := fun n => ρ ^ ((Int.natAbs n) ^ 2)
  have hρ_nonneg : 0 ≤ ρ := hρ_pos.le
  have htail_geom : Summable (fun n : ℕ => ρ ^ (1 + 3 * n)) := by
    have hρ_cube : ρ ^ 3 < 1 := by
      simpa using
        (pow_lt_pow_left₀ hρ_lt_one hρ_nonneg
          (by norm_num : (3 : ℕ) ≠ 0))
    have hbase : Summable (fun n : ℕ => (ρ ^ 3) ^ n) :=
      summable_geometric_of_lt_one (by positivity) hρ_cube
    have hmul : Summable (fun n : ℕ => ρ * (ρ ^ 3) ^ n) :=
      hbase.mul_left ρ
    simpa [pow_add, pow_mul] using hmul
  have hbound (n : ℕ) :
      ρ ^ ((n + 1) ^ 2) ≤ ρ ^ (1 + 3 * n) := by
    apply pow_le_pow_of_le_one hρ_nonneg hρ_lt_one.le
    cases n with
    | zero => norm_num
    | succ n =>
        nlinarith [Nat.zero_le n]
  have htail : Summable (fun n : ℕ => ρ ^ ((n + 1) ^ 2)) :=
    htail_geom.of_nonneg_of_le (fun n => by positivity) hbound
  have hpos : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)) := by
    apply htail.congr
    intro n
    change ρ ^ ((n + 1) ^ 2) =
      ρ ^ ((Int.natAbs ((n + 1 : ℕ) : ℤ)) ^ 2)
    rw [Int.natAbs_natCast]
  have hneg : Summable (fun n : ℕ => f (-((n + 1 : ℕ) : ℤ))) := by
    apply hpos.congr
    intro n
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
      norm_num
    simp only [f, hcast]
    rw [Int.natAbs_neg]
  have hf : Summable f := Summable.of_add_one_of_neg_add_one hpos hneg
  have hf_even : f.Even := by
    intro n
    simp [f]
  have hpnat :
      (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, ρ ^ ((n + 1) ^ 2) := by
    calc
      (∑' n : ℕ+, f (n : ℤ)) =
          ∑' n : ℕ, f ((n + 1 : ℕ) : ℤ) := by
        simpa using
          (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (n : ℤ)))
      _ = ∑' n : ℕ, ρ ^ ((n + 1) ^ 2) := by
        apply tsum_congr
        intro n
        change ρ ^ ((Int.natAbs ((n + 1 : ℕ) : ℤ)) ^ 2) =
          ρ ^ ((n + 1) ^ 2)
        rw [Int.natAbs_natCast]
  have hreal :
      (∑' n : ℤ, f n) = 1 + 2 * (∑' n : ℕ, ρ ^ ((n + 1) ^ 2)) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hf_even hf, hpnat]
    simp [f]
  have htail_bound :
      (∑' n : ℕ, ρ ^ ((n + 1) ^ 2)) ≤ ρ / (1 - ρ ^ 3) :=
    gaussianImage_geometricTail ρ hρ_pos hρ_lt_one
  have hreal_bound :
      (∑' n : ℤ, f n) ≤ 1 + 2 * ρ / (1 - ρ ^ 3) := by
    rw [hreal]
    calc
      1 + 2 * (∑' n : ℕ, ρ ^ ((n + 1) ^ 2)) ≤
          1 + 2 * (ρ / (1 - ρ ^ 3)) := by
        simpa [add_comm] using
          (add_le_add_left
            (mul_le_mul_of_nonneg_left htail_bound
              (by norm_num : (0 : ℝ) ≤ 2)) 1)
      _ = 1 + 2 * ρ / (1 - ρ ^ 3) := by ring
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf]
  exact ENNReal.ofReal_mono hreal_bound

/-- The same two-sided estimate in the exponential form used by periodization. -/
theorem integerGaussian_exp_geometricTail
    (c : ℝ) (hc : 0 < c) :
    ∑' n : ℤ, ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2)) ≤
      ENNReal.ofReal
        (1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) := by
  let ρ : ℝ := Real.exp (-c)
  have hρ_pos : 0 < ρ := by
    exact Real.exp_pos _
  have hρ_lt_one : ρ < 1 := by
    dsimp [ρ]
    exact (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have hρ := integerGaussian_geometricTail ρ hρ_pos hρ_lt_one
  calc
    ∑' n : ℤ, ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2)) =
        ∑' n : ℤ, ENNReal.ofReal (ρ ^ (Int.natAbs n) ^ 2) := by
      apply tsum_congr
      intro n
      dsimp [ρ]
      congr 1
      have hsq : (n : ℝ) ^ 2 = ((Int.natAbs n : ℕ) : ℝ) ^ 2 := by
        have habs : |(n : ℝ)| = ((Int.natAbs n : ℕ) : ℝ) := by
          symm
          calc
            ((Int.natAbs n : ℕ) : ℝ) = ((Int.natAbs n : ℤ) : ℝ) := by
              norm_num
            _ = |(n : ℝ)| := by
              simp only [Int.natCast_natAbs, Int.cast_abs]
        calc
          (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
          _ = ((Int.natAbs n : ℕ) : ℝ) ^ 2 := by rw [habs]
      rw [hsq]
      rw [← Real.exp_nat_mul]
      rw [Nat.cast_pow]
      ring_nf
    _ ≤ ENNReal.ofReal (1 + 2 * ρ / (1 - ρ ^ 3)) := hρ
    _ = ENNReal.ofReal
        (1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) := by
      rfl

/-! The exponential image estimate with the zero image removed. -/
theorem integerGaussian_exp_nonzero_geometricTail
    (c : ℝ) (hc : 0 < c) :
    (∑' n : ℤ,
        (if n = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2)))) ≤
      ENNReal.ofReal
        (2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) := by
  have hfull := integerGaussian_exp_geometricTail c hc
  rw [ENNReal.tsum_eq_add_tsum_ite (f := fun n : ℤ =>
    ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2))) 0] at hfull
  have hzero :
      ENNReal.ofReal (Real.exp (-c * ((0 : ℤ) : ℝ) ^ 2)) =
        ENNReal.ofReal (1 : ℝ) := by
    norm_num
  rw [hzero] at hfull
  have hsplit :
      ENNReal.ofReal
          (1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) =
        ENNReal.ofReal (1 : ℝ) +
          ENNReal.ofReal (2 * Real.exp (-c) /
            (1 - (Real.exp (-c)) ^ 3)) := by
    have hρ : Real.exp (-c) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc)
    have hρcube : (Real.exp (-c)) ^ 3 < 1 := by
      simpa using
        (pow_lt_pow_left₀ hρ (Real.exp_pos (-c)).le
          (by norm_num : (3 : ℕ) ≠ 0))
    have htail_nonneg :
        0 ≤ 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) := by
      positivity
    rw [ENNReal.ofReal_add (by norm_num) htail_nonneg]
  rw [hsplit] at hfull
  have hcancel :=
    (ENNReal.add_le_add_iff_left (a := ENNReal.ofReal (1 : ℝ))
      ENNReal.ofReal_ne_top).mp hfull
  simpa using hcancel

/-- The nonzero images of a shifted integer Gaussian split into two geometric
tails with different orientations. -/
theorem integerShiftedGaussian_exp_nonzero_geometricTail
    (alpha B : ℝ) (halpha : 0 < alpha) (hB : 1 < B) :
    (∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
      ENNReal.ofReal (Real.exp (-alpha * ((n : ℝ) * B - 1) ^ 2))) ≤
      ENNReal.ofReal
        (Real.exp (-alpha * (B - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
          Real.exp (-alpha * (B + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))) := by
  let cp := alpha * (3 * B ^ 2 - 2 * B)
  let cn := alpha * (3 * B ^ 2 + 2 * B)
  let ep := Real.exp (-alpha * (B - 1) ^ 2)
  let en := Real.exp (-alpha * (B + 1) ^ 2)
  let p : ℕ → ℝ := fun n =>
    Real.exp (-alpha * (((n : ℝ) + 1) * B - 1) ^ 2)
  let m : ℕ → ℝ := fun n =>
    Real.exp (-alpha * (((n : ℝ) + 1) * B + 1) ^ 2)
  have hBpos : 0 < B := lt_trans (by norm_num) hB
  have hcp : 0 < cp := by
    dsimp [cp]
    have : 0 < B * (3 * B - 2) := mul_pos hBpos (by nlinarith)
    nlinarith
  have hcn : 0 < cn := by
    dsimp [cn]
    have : 0 < B * (3 * B + 2) := mul_pos hBpos (by nlinarith)
    nlinarith
  have hrp : 0 ≤ Real.exp (-cp) := Real.exp_nonneg _
  have hrn : 0 ≤ Real.exp (-cn) := Real.exp_nonneg _
  have hrp_lt : Real.exp (-cp) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hcp)
  have hrn_lt : Real.exp (-cn) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hcn)
  have hp_bound (n : ℕ) : p n ≤ ep * Real.exp (-cp) ^ n := by
    have hquad : (B - 1) ^ 2 + (n : ℝ) * (3 * B ^ 2 - 2 * B) ≤
        ((n + 1 : ℝ) * B - 1) ^ 2 := by
      cases n with
      | zero => norm_num
      | succ k =>
          have hgap : 0 ≤ ((k : ℝ) + 1) * (k : ℝ) * B ^ 2 := by positivity
          push_cast
          nlinarith
    rw [show ep * Real.exp (-cp) ^ n =
        Real.exp (-alpha * ((B - 1) ^ 2 + (n : ℝ) *
          (3 * B ^ 2 - 2 * B))) by
      dsimp [ep, cp]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hquad (by linarith))
  have hm_bound (n : ℕ) : m n ≤ en * Real.exp (-cn) ^ n := by
    have hquad : (B + 1) ^ 2 + (n : ℝ) * (3 * B ^ 2 + 2 * B) ≤
        ((n + 1 : ℝ) * B + 1) ^ 2 := by
      cases n with
      | zero => norm_num
      | succ k =>
          have hgap : 0 ≤ ((k : ℝ) + 1) * (k : ℝ) * B ^ 2 := by positivity
          push_cast
          nlinarith
    rw [show en * Real.exp (-cn) ^ n =
        Real.exp (-alpha * ((B + 1) ^ 2 + (n : ℝ) *
          (3 * B ^ 2 + 2 * B))) by
      dsimp [en, cn]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hquad (by linarith))
  have hgp : Summable (fun n : ℕ => ep * Real.exp (-cp) ^ n) :=
    (summable_geometric_of_lt_one hrp hrp_lt).mul_left ep
  have hgn : Summable (fun n : ℕ => en * Real.exp (-cn) ^ n) :=
    (summable_geometric_of_lt_one hrn hrn_lt).mul_left en
  have hp : Summable p :=
    hgp.of_nonneg_of_le (fun _ => Real.exp_nonneg _) hp_bound
  have hm : Summable m :=
    hgn.of_nonneg_of_le (fun _ => Real.exp_nonneg _) hm_bound
  have hp_sum : ∑' n, p n ≤ ep / (1 - Real.exp (-cp)) := by
    calc
      ∑' n, p n ≤ ∑' n, ep * Real.exp (-cp) ^ n :=
        hp.tsum_le_tsum hp_bound hgp
      _ = ep * (1 - Real.exp (-cp))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hrp hrp_lt]
      _ = ep / (1 - Real.exp (-cp)) := rfl
  have hm_sum : ∑' n, m n ≤ en / (1 - Real.exp (-cn)) := by
    calc
      ∑' n, m n ≤ ∑' n, en * Real.exp (-cn) ^ n :=
        hm.tsum_le_tsum hm_bound hgn
      _ = en * (1 - Real.exp (-cn))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hrn hrn_lt]
      _ = en / (1 - Real.exp (-cn)) := rfl
  let f : ℤ → ℝ := fun n => if n = 0 then 0 else
    Real.exp (-alpha * ((n : ℝ) * B - 1) ^ 2)
  have hfpos : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    apply hp.congr
    intro n
    dsimp [f, p]
    rw [if_neg (by omega : (n : ℤ) + 1 ≠ 0)]
    push_cast
    rfl
  have hfneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    apply hm.congr
    intro n
    dsimp [f, m]
    rw [if_neg (by omega : -((n : ℤ) + 1) ≠ 0)]
    push_cast
    congr 2
    ring_nf
  have hf : Summable f := Summable.of_add_one_of_neg_add_one hfpos hfneg
  have hposPnat : (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, p n := by
    calc
      (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, f ((n : ℤ) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (n : ℤ)))
      _ = ∑' n : ℕ, p n := by
        apply tsum_congr
        intro n
        dsimp [f, p]
        rw [if_neg (by omega : (n : ℤ) + 1 ≠ 0)]
        push_cast
        rfl
  have hnegPnat : (∑' n : ℕ+, f (-(n : ℤ))) = ∑' n : ℕ, m n := by
    calc
      (∑' n : ℕ+, f (-(n : ℤ))) =
          ∑' n : ℕ, f (-((n : ℤ) + 1)) := by
        simpa only using
          (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (-(n : ℤ)))) |>.trans (by
            apply tsum_congr
            intro n
            rw [show -(((n + 1 : ℕ) : ℤ)) = -((n : ℤ) + 1) by omega])
      _ = ∑' n : ℕ, m n := by
        apply tsum_congr
        intro n
        dsimp [f, m]
        rw [if_neg (by omega : -((n : ℤ) + 1) ≠ 0)]
        push_cast
        congr 2
        ring_nf
  have hfsum : ∑' n : ℤ, f n = (∑' n, p n) + ∑' n, m n := by
    rw [tsum_int_eq_zero_add_tsum_pnat hf]
    simp only [f, if_pos, zero_add]
    rw [hposPnat, hnegPnat]
  rw [show (∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
      ENNReal.ofReal (Real.exp (-alpha * ((n : ℝ) * B - 1) ^ 2))) =
      ∑' n : ℤ, ENNReal.ofReal (f n) by
    apply tsum_congr
    intro n
    by_cases hn : n = 0 <;> simp [f, hn]]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n : ℤ => by
    by_cases hn : n = 0
    · simp [f, hn]
    · simp only [f, if_neg hn]
      exact Real.exp_nonneg _) hf]
  apply ENNReal.ofReal_mono
  rw [hfsum]
  simpa [ep, en, cp, cn] using add_le_add hp_sum hm_sum

end CertifiedProjections
