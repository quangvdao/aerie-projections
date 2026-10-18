/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Arithmetic.Transcendental.SquareRoot.SqrtData
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Sqrt

/-!
# Certified square-root intervals

The executable square root is the integer square root of the scaled endpoint.
The upper endpoint adds one exactly when the radicand is not a square.  Its
soundness theorem reduces to the two defining inequalities for `Nat.sqrt`.
-/

namespace CertifiedProjections
namespace Interval

variable {p : ℕ}

private theorem sqrt_sq_le (n : ℕ) : Nat.sqrt n ^ 2 ≤ n :=
  Nat.sqrt_le' n

private theorem le_ceilSqrt_sq (n : ℕ) : n ≤ ceilSqrt n ^ 2 := by
  by_cases h : Nat.sqrt n * Nat.sqrt n = n
  · simp [ceilSqrt, Nat.pow_two, h]
  · have hlt := Nat.lt_succ_sqrt' n
    simp only [ceilSqrt, h, if_false]
    exact hlt.le

/-- A strictly positive raw lower endpoint remains strictly positive after
the outward square-root operation. -/
theorem sqrt_lo_pos_of_lo_pos {I : Interval p} (hlo : 0 < I.lo) :
    0 < I.sqrt.lo := by
  unfold sqrt Internal.sqrtRadicand
  simp only
  have hloNat : 0 < I.lo.toNat := by omega
  exact_mod_cast (Nat.sqrt_pos.2
    (Nat.mul_pos hloNat (Dyadic.scale_pos p)))

theorem contains_sqrt {I : Interval p} {x : ℝ}
    (hlo : 0 ≤ I.lo) (hx : I.Contains x) :
    I.sqrt.Contains (Real.sqrt x) := by
  have hvalid : I.Valid := valid_of_contains hx
  have hhi : 0 ≤ I.hi := hlo.trans hvalid
  have hspos : (0 : ℝ) < Dyadic.scale p := by
    exact_mod_cast Dyadic.scale_pos p
  have hsnonneg : (0 : ℝ) ≤ Dyadic.scale p := hspos.le
  have hloNat : (I.lo.toNat : ℤ) = I.lo := Int.toNat_of_nonneg hlo
  have hhiNat : (I.hi.toNat : ℤ) = I.hi := Int.toNat_of_nonneg hhi
  have hlNat := sqrt_sq_le (Internal.sqrtRadicand p I.lo)
  have huNat := le_ceilSqrt_sq (Internal.sqrtRadicand p I.hi)
  have hlScaled :
      ((Nat.sqrt (Internal.sqrtRadicand p I.lo) : ℕ) : ℝ) ^ 2 ≤
        (I.lo : ℝ) * Dyadic.scale p := by
    rw [Internal.sqrtRadicand] at hlNat
    rw [← hloNat]
    exact_mod_cast hlNat
  have huScaled :
      (I.hi : ℝ) * Dyadic.scale p ≤
        (ceilSqrt (Internal.sqrtRadicand p I.hi) : ℝ) ^ 2 := by
    rw [Internal.sqrtRadicand] at huNat
    rw [← hhiNat]
    exact_mod_cast huNat
  have hlSq :
      (Dyadic.toReal p (Nat.sqrt (Internal.sqrtRadicand p I.lo) : ℕ)) ^ 2 ≤
        Dyadic.toReal p I.lo := by
    rw [Dyadic.toReal, Dyadic.toReal, div_pow]
    calc
      (↑(Nat.sqrt (Internal.sqrtRadicand p I.lo)) : ℝ) ^ 2 /
          (↑(Dyadic.scale p) : ℝ) ^ 2 ≤
          ((I.lo : ℝ) * Dyadic.scale p) / (Dyadic.scale p : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hlScaled (sq_nonneg _)
      _ = (I.lo : ℝ) / Dyadic.scale p := by field_simp
  have huSq :
      Dyadic.toReal p I.hi ≤
        (Dyadic.toReal p (ceilSqrt (Internal.sqrtRadicand p I.hi) : ℕ)) ^ 2 := by
    rw [Dyadic.toReal, Dyadic.toReal, div_pow]
    calc
      (I.hi : ℝ) / Dyadic.scale p =
          ((I.hi : ℝ) * Dyadic.scale p) / (Dyadic.scale p : ℝ) ^ 2 := by
        field_simp
      _ ≤ (↑(ceilSqrt (Internal.sqrtRadicand p I.hi)) : ℝ) ^ 2 /
          (↑(Dyadic.scale p) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right huScaled (sq_nonneg _)
  have hx0 : 0 ≤ x := (by
    have hdecode : 0 ≤ Dyadic.toReal p I.lo :=
      div_nonneg (by exact_mod_cast hlo) hsnonneg
    exact hdecode.trans hx.1)
  have hlEndpoint :
      0 ≤ Dyadic.toReal p (Nat.sqrt (Internal.sqrtRadicand p I.lo) : ℕ) :=
    div_nonneg (by positivity) hsnonneg
  have huEndpoint :
      0 ≤ Dyadic.toReal p (ceilSqrt (Internal.sqrtRadicand p I.hi) : ℕ) :=
    div_nonneg (by positivity) hsnonneg
  constructor
  · apply (Real.le_sqrt hlEndpoint hx0).mpr
    exact hlSq.trans hx.1
  · apply Real.sqrt_le_iff.mpr
    refine ⟨huEndpoint, ?_⟩
    exact hx.2.trans huSq

end Interval
end CertifiedProjections
