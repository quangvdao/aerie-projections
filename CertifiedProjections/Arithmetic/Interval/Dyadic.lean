/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Fixed-precision dyadic endpoints

The numerical certificates use signed integer numerators over one common
power-of-two denominator.  This module keeps that representation executable
and proves the two rounding facts used by every later interval operation.
-/

namespace CertifiedProjections
namespace Dyadic

/-- The positive common denominator at precision `p`. -/
def scale (p : ℕ) : ℕ := 2 ^ p

/-- Interpret an integer numerator as a rational dyadic at precision `p`. -/
def toRat (p : ℕ) (n : ℤ) : ℚ := (n : ℚ) / (scale p : ℚ)

/-- Interpret an integer numerator as a real dyadic at precision `p`. -/
noncomputable def toReal (p : ℕ) (n : ℤ) : ℝ :=
  (n : ℝ) / (scale p : ℝ)

/-- Round a rational downward to the precision-`p` dyadic grid. -/
def roundDown (p : ℕ) (x : ℚ) : ℤ := ⌊x * scale p⌋

/-- Round a rational upward to the precision-`p` dyadic grid. -/
def roundUp (p : ℕ) (x : ℚ) : ℤ := ⌈x * scale p⌉

/-- Floor division by the positive precision scale. -/
def floorDiv (p : ℕ) (n : ℤ) : ℤ := n / (scale p : ℤ)

/-- Ceiling division by the positive precision scale. -/
def ceilDiv (p : ℕ) (n : ℤ) : ℤ := -((-n) / (scale p : ℤ))

/-- Floor division by an arbitrary integer denominator. -/
def floorDivBy (n d : ℤ) : ℤ := n / d

/-- Ceiling division by an arbitrary integer denominator. -/
def ceilDivBy (n d : ℤ) : ℤ := -((-n) / d)

@[simp]
theorem scale_pos (p : ℕ) : 0 < scale p := by
  simp [scale]

@[simp]
theorem scale_ne_zero (p : ℕ) : scale p ≠ 0 :=
  (scale_pos p).ne'

@[simp]
theorem toRat_zero (p : ℕ) : toRat p 0 = 0 := by
  simp [toRat]

@[simp]
theorem toReal_zero (p : ℕ) : toReal p 0 = 0 := by
  simp [toReal]

@[simp]
theorem toRat_neg (p : ℕ) (n : ℤ) : toRat p (-n) = -toRat p n := by
  simp only [toRat, Int.cast_neg]
  ring

@[simp]
theorem toReal_neg (p : ℕ) (n : ℤ) : toReal p (-n) = -toReal p n := by
  simp only [toReal, Int.cast_neg]
  ring

theorem toRat_add (p : ℕ) (m n : ℤ) :
    toRat p (m + n) = toRat p m + toRat p n := by
  simp only [toRat, Int.cast_add]
  ring

theorem toReal_add (p : ℕ) (m n : ℤ) :
    toReal p (m + n) = toReal p m + toReal p n := by
  simp only [toReal, Int.cast_add]
  ring

theorem cast_toRat (p : ℕ) (n : ℤ) :
    ((toRat p n : ℚ) : ℝ) = toReal p n := by
  norm_num [toRat, toReal]

theorem toRat_mono {p : ℕ} {m n : ℤ} (h : m ≤ n) :
    toRat p m ≤ toRat p n := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast h)
    (by exact_mod_cast (scale_pos p).le : (0 : ℚ) ≤ (scale p : ℚ))

theorem toReal_mono {p : ℕ} {m n : ℤ} (h : m ≤ n) :
    toReal p m ≤ toReal p n := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast h)
    (by exact_mod_cast (scale_pos p).le : (0 : ℝ) ≤ (scale p : ℝ))

theorem roundDown_spec (p : ℕ) (x : ℚ) :
    toRat p (roundDown p x) ≤ x := by
  have h := Int.floor_le (x * scale p)
  rw [toRat, div_le_iff₀ (by exact_mod_cast scale_pos p : (0 : ℚ) < (scale p : ℚ))]
  simpa [roundDown, mul_comm] using h

theorem roundUp_spec (p : ℕ) (x : ℚ) :
    x ≤ toRat p (roundUp p x) := by
  have h := Int.le_ceil (x * scale p)
  rw [toRat, le_div_iff₀ (by exact_mod_cast scale_pos p : (0 : ℚ) < (scale p : ℚ))]
  simpa [roundUp, mul_comm] using h

theorem roundDown_spec_real (p : ℕ) (x : ℚ) :
    toReal p (roundDown p x) ≤ (x : ℝ) := by
  rw [← cast_toRat]
  exact_mod_cast (roundDown_spec p x)

theorem roundUp_spec_real (p : ℕ) (x : ℚ) :
    (x : ℝ) ≤ toReal p (roundUp p x) := by
  rw [← cast_toRat]
  exact_mod_cast (roundUp_spec p x)

theorem floorDiv_spec_real (p : ℕ) (n : ℤ) :
    toReal p (floorDiv p n) ≤
      (n : ℝ) / (scale p : ℝ) ^ 2 := by
  have hs0 : (scale p : ℤ) ≠ 0 := by
    exact_mod_cast scale_ne_zero p
  have hInt : floorDiv p n * (scale p : ℤ) ≤ n :=
    Int.ediv_mul_le n hs0
  have hReal :
      (floorDiv p n : ℝ) * (scale p : ℝ) ≤ n := by
    exact_mod_cast hInt
  rw [toReal]
  calc
    (floorDiv p n : ℝ) / scale p =
        ((floorDiv p n : ℝ) * scale p) / (scale p : ℝ) ^ 2 := by
      field_simp
    _ ≤ (n : ℝ) / (scale p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hReal (sq_nonneg _)

theorem ceilDiv_spec_real (p : ℕ) (n : ℤ) :
    (n : ℝ) / (scale p : ℝ) ^ 2 ≤
      toReal p (ceilDiv p n) := by
  have hs0 : (scale p : ℤ) ≠ 0 := by
    exact_mod_cast scale_ne_zero p
  have hFloor : ((-n) / (scale p : ℤ)) * (scale p : ℤ) ≤ -n :=
    Int.ediv_mul_le (-n) hs0
  have hInt : n ≤ ceilDiv p n * (scale p : ℤ) := by
    calc
      n = -(-n) := by simp
      _ ≤ -(((-n) / (scale p : ℤ)) * (scale p : ℤ)) :=
        neg_le_neg hFloor
      _ = ceilDiv p n * (scale p : ℤ) := by simp [ceilDiv]
  have hReal :
      (n : ℝ) ≤ (ceilDiv p n : ℝ) * (scale p : ℝ) := by
    exact_mod_cast hInt
  rw [toReal]
  calc
    (n : ℝ) / (scale p : ℝ) ^ 2 ≤
        ((ceilDiv p n : ℝ) * scale p) / (scale p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hReal (sq_nonneg _)
    _ = (ceilDiv p n : ℝ) / scale p := by field_simp

theorem floorDivBy_spec_real (n : ℤ) {d : ℤ} (hd : 0 < d) :
    (floorDivBy n d : ℝ) ≤ (n : ℝ) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < (d : ℝ))]
  exact_mod_cast Int.ediv_mul_le n hd.ne'

theorem ceilDivBy_spec_real (n : ℤ) {d : ℤ} (hd : 0 < d) :
    (n : ℝ) / d ≤ (ceilDivBy n d : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < (d : ℝ))]
  have hFloor : ((-n) / d) * d ≤ -n := Int.ediv_mul_le (-n) hd.ne'
  have hCeil : n ≤ ceilDivBy n d * d := by
    calc
      n = -(-n) := by simp
      _ ≤ -(((-n) / d) * d) := neg_le_neg hFloor
      _ = ceilDivBy n d * d := by simp [ceilDivBy]
  exact_mod_cast hCeil

theorem roundDown_nonneg {p : ℕ} {x : ℚ} (hx : 0 ≤ x) :
    0 ≤ roundDown p x := by
  rw [roundDown, Int.floor_nonneg]
  exact mul_nonneg hx (by positivity)

/-- A rational at least one grid unit above zero rounds down positively. -/
theorem roundDown_pos {p : ℕ} {x : ℚ}
    (hx : 1 ≤ x * scale p) :
    0 < roundDown p x := by
  rw [roundDown, Int.floor_pos]
  exact hx

theorem roundUp_le_scale {p : ℕ} {x : ℚ} (hx : x ≤ 1) :
    roundUp p x ≤ scale p := by
  rw [roundUp, Int.ceil_le]
  simpa using mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℚ) ≤ scale p)

@[simp]
theorem toRat_scale (p : ℕ) : toRat p (scale p) = 1 := by
  simp [toRat, scale_ne_zero]

@[simp]
theorem roundDown_dyadic (p : ℕ) (n : ℤ) :
    roundDown p (toRat p n) = n := by
  rw [roundDown, toRat, div_mul_cancel₀]
  · simp
  · exact_mod_cast scale_ne_zero p

@[simp]
theorem roundUp_dyadic (p : ℕ) (n : ℤ) :
    roundUp p (toRat p n) = n := by
  rw [roundUp, toRat, div_mul_cancel₀]
  · simp
  · exact_mod_cast scale_ne_zero p

@[simp]
theorem roundDown_one (p : ℕ) : roundDown p 1 = scale p := by
  rw [← toRat_scale p, roundDown_dyadic]

@[simp]
theorem roundUp_one (p : ℕ) : roundUp p 1 = scale p := by
  rw [← toRat_scale p, roundUp_dyadic]

end Dyadic
end CertifiedProjections
