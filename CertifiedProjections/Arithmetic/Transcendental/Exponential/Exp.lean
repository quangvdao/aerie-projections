/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Arithmetic.Transcendental.Exponential.ExpData
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Certified exponential upper enclosures

The paper artifact bounds exponentials by scaling an argument to `x / 2^k`,
applying `1 + t ≤ exp t`, taking reciprocals, and squaring `k` times.  This
module proves exactly that algorithm.  There is no floating-point evaluation
and no unproved Taylor oracle.
-/

namespace CertifiedProjections

namespace Exp

variable {p : ℕ}

private theorem neg_upper_real {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n) :
    Real.exp (-x) ≤ ((1 + x / n)⁻¹) ^ n := by
  have ht : 0 ≤ x / (n : ℝ) := div_nonneg hx (by positivity)
  have hbase :
      Real.exp (-(x / n)) ≤ (1 + x / n)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr <|
      by simpa [add_comm] using Real.add_one_le_exp (x / n)
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hbase n
  calc
    Real.exp (-x) = Real.exp ((n : ℝ) * (-(x / n))) := by
      congr 1
      field_simp
    _ = Real.exp (-(x / n)) ^ n := Real.exp_nat_mul _ _
    _ ≤ ((1 + x / n)⁻¹) ^ n := hpow

private theorem pos_upper_real {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hxn : x < n) :
    Real.exp x ≤ ((1 - x / n)⁻¹) ^ n := by
  have hn : 0 < n := by
    by_contra hn0
    simp only [not_lt, Nat.le_zero] at hn0
    subst n
    exact (not_lt_of_ge hx) (by simpa using hxn)
  have ht : x / (n : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hxn
  have hbase :
      Real.exp (x / n) ≤ (1 - x / n)⁻¹ := by
    calc
      Real.exp (x / n) = (Real.exp (-(x / n)))⁻¹ := by
        simpa using Real.exp_neg (-(x / n))
      _ ≤ (1 - x / n)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (sub_pos.mpr ht)).mpr <|
          by linarith [Real.add_one_le_exp (-(x / n))]
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hbase n
  calc
    Real.exp x = Real.exp ((n : ℝ) * (x / n)) := by
      congr 1
      field_simp
    _ = Real.exp (x / n) ^ n := Real.exp_nat_mul _ _
    _ ≤ ((1 - x / n)⁻¹) ^ n := hpow

private theorem neg_argument_interval_pos {p k : ℕ} {x : ℚ} (hx : 0 ≤ x) :
    0 < (Interval.ofRat p 1 + Interval.ofRat p (x / (2 ^ k : ℕ))).lo := by
  change 0 < Dyadic.roundDown p 1 +
    Dyadic.roundDown p (x / (2 ^ k : ℕ))
  rw [Dyadic.roundDown_one]
  have harg : 0 ≤ x / (2 ^ k : ℕ) := div_nonneg hx (by positivity)
  exact add_pos_of_pos_of_nonneg (by exact_mod_cast Dyadic.scale_pos p)
    (Dyadic.roundDown_nonneg harg)

theorem negUpper_contains {p k : ℕ} {x : ℚ} (hx : 0 ≤ x) :
    (negUpper p x k).Contains (Real.exp (-x)) := by
  let argument := x / (2 ^ k : ℕ)
  have harg : (Interval.ofRat p argument).Contains (argument : ℝ) :=
    Interval.contains_ofRat p argument
  have hone : (Interval.ofRat p 1).Contains (1 : ℝ) :=
    by simpa using Interval.contains_ofRat p (1 : ℚ)
  have hsum :
      (Interval.ofRat p 1 + Interval.ofRat p argument).Contains
        (1 + (argument : ℝ)) :=
    Interval.contains_add hone harg
  have hrecip :
      (negBase p x k).Contains ((1 + (argument : ℝ))⁻¹) := by
    apply Interval.contains_reciprocal_of_pos
    · exact neg_argument_interval_pos hx
    · simpa [negBase, argument] using hsum
  have hpow := Interval.contains_squareN hrecip k
  have hupper :
      Real.exp (-(x : ℝ)) ≤
        Interval.iterSquare ((1 + (argument : ℝ))⁻¹) k := by
    rw [Interval.iterSquare_eq_pow_two_pow]
    simpa [argument] using
      neg_upper_real (x := (x : ℝ)) (by exact_mod_cast hx) (2 ^ k) (by positivity)
  simpa only [negUpper, upperHull, Interval.Contains, Dyadic.toReal_zero] using
    And.intro (Real.exp_nonneg (-(x : ℝ))) (hupper.trans hpow.2)

theorem posUpper_contains {p k : ℕ} {x : ℚ}
    (hx : 0 ≤ x) (hupper : x < (2 ^ k : ℕ))
    (hbase : 0 < (Interval.ofRat p (1 - x / (2 ^ k : ℕ))).lo) :
    (posUpper p x k).Contains (Real.exp x) := by
  let argument := x / (2 ^ k : ℕ)
  have hdiff :
      (Interval.ofRat p (1 - argument)).Contains
        (1 - (argument : ℝ)) := by
    simpa using Interval.contains_ofRat p (1 - argument)
  have hrecip :
      (posBase p x k).Contains ((1 - (argument : ℝ))⁻¹) := by
    apply Interval.contains_reciprocal_of_pos
    · simpa [argument] using hbase
    · simpa [posBase, argument] using hdiff
  have hpow := Interval.contains_squareN hrecip k
  have hupperReal :
      Real.exp (x : ℝ) ≤
        Interval.iterSquare ((1 - (argument : ℝ))⁻¹) k := by
    rw [Interval.iterSquare_eq_pow_two_pow]
    simpa [argument] using
      pos_upper_real (x := (x : ℝ)) (n := 2 ^ k)
        (by exact_mod_cast hx) (by exact_mod_cast hupper)
  simpa only [posUpper, upperHull, Interval.Contains, Dyadic.toReal_zero] using
    And.intro (Real.exp_nonneg (x : ℝ)) (hupperReal.trans hpow.2)

/--
Soundness of the signed rational exponential enclosure.  Only the positive
branch needs the scaling and reciprocal-base side conditions.
-/
theorem upper_contains {p k : ℕ} {x : ℚ}
    (hupper : 0 ≤ x → x < (2 ^ k : ℕ))
    (hbase : 0 ≤ x →
      0 < (Interval.ofRat p
        (1 - x / (2 ^ k : ℕ))).lo) :
    (upper p x k).Contains (Real.exp x) := by
  by_cases hx : 0 ≤ x
  · rw [upper, if_pos hx]
    exact posUpper_contains hx (hupper hx) (hbase hx)
  · rw [upper, if_neg hx]
    have hneg : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
    have h := negUpper_contains (p := p) (k := k) hneg
    simpa using h

/--
Soundness of `ofIntervalUpper`.  The two executable side conditions mention
only the rational upper endpoint and are therefore discharged by reflected
certificate checks.
-/
theorem ofIntervalUpper_contains {p k : ℕ} {I : Interval p} {x : ℝ}
    (hx : I.Contains x)
    (hupper : 0 ≤ I.upperRat →
      I.upperRat < (2 ^ k : ℕ))
    (hbase : 0 ≤ I.upperRat →
      0 < (Interval.ofRat p
        (1 - I.upperRat / (2 ^ k : ℕ))).lo) :
    (ofIntervalUpper p I k).Contains (Real.exp x) := by
  have hq :=
    upper_contains (p := p) (k := k)
      (x := I.upperRat) hupper hbase
  have hxq : x ≤ (I.upperRat : ℝ) := by
    simpa only [Interval.upperRat, Dyadic.cast_toRat] using hx.2
  have hlo : (ofIntervalUpper p I k).lo = 0 := by
    unfold ofIntervalUpper upper posUpper negUpper upperHull
    split <;> rfl
  exact ⟨
    by
      rw [hlo, Dyadic.toReal_zero]
      exact Real.exp_nonneg x,
    (Real.exp_le_exp.mpr hxq).trans hq.2⟩

end Exp
end CertifiedProjections
