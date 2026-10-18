/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Arithmetic.Interval.Dyadic
import Mathlib.Tactic.Ring

/-!
# Sound dyadic interval arithmetic

`Interval p` is deliberately raw data: two signed numerators sharing the
denominator `2^p`.  Endpoint order is a separate proposition.  Arithmetic
rounds exact rational corner bounds outward and is proved sound for real
containment.
-/

namespace CertifiedProjections

/-- A closed interval whose endpoints share the dyadic denominator `2^p`. -/
structure Interval (p : ℕ) where
  /-- Signed numerator of the lower endpoint. -/
  lo : ℤ
  /-- Signed numerator of the upper endpoint. -/
  hi : ℤ
deriving DecidableEq

namespace Interval

variable {p : ℕ}

/-- The raw endpoints occur in increasing order. -/
abbrev Valid (I : Interval p) : Prop := I.lo ≤ I.hi

/-- A real number lies between the decoded dyadic endpoints. -/
def Contains (I : Interval p) (x : ℝ) : Prop :=
  Dyadic.toReal p I.lo ≤ x ∧ x ≤ Dyadic.toReal p I.hi

/-- The lower endpoint decoded as a rational. -/
def lowerRat (I : Interval p) : ℚ := Dyadic.toRat p I.lo

/-- The upper endpoint decoded as a rational. -/
def upperRat (I : Interval p) : ℚ := Dyadic.toRat p I.hi

/-- Outward-round exact rational lower and upper bounds. -/
def enclose (p : ℕ) (lower upper : ℚ) : Interval p :=
  ⟨Dyadic.roundDown p lower, Dyadic.roundUp p upper⟩

/-- The smallest grid enclosure produced from one rational. -/
def ofRat (p : ℕ) (x : ℚ) : Interval p := enclose p x x

/-- Exact interval addition on a common dyadic grid. -/
def add (I J : Interval p) : Interval p :=
  ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Exact interval negation on a common dyadic grid. -/
def neg (I : Interval p) : Interval p := ⟨-I.hi, -I.lo⟩

/-- Outward interval hull for the absolute value. The zero lower endpoint is
intentional: it is sound uniformly, including cells that cross zero. -/
def absHull (I : Interval p) : Interval p :=
  ⟨0, max (-I.lo) I.hi⟩

/-- Exact interval subtraction followed by no additional rounding. -/
def sub (I J : Interval p) : Interval p := add I (neg J)

instance instAddInterval : Add (Interval p) := ⟨add⟩
instance instNegInterval : Neg (Interval p) := ⟨neg⟩
instance instSubInterval : Sub (Interval p) := ⟨sub⟩

@[simp] theorem add_lo (I J : Interval p) : (I + J).lo = I.lo + J.lo := rfl
@[simp] theorem add_hi (I J : Interval p) : (I + J).hi = I.hi + J.hi := rfl
@[simp] theorem neg_lo (I : Interval p) : (-I).lo = -I.hi := rfl
@[simp] theorem neg_hi (I : Interval p) : (-I).hi = -I.lo := rfl
@[simp] theorem absHull_lo (I : Interval p) : I.absHull.lo = 0 := rfl
@[simp] theorem absHull_hi (I : Interval p) :
    I.absHull.hi = max (-I.lo) I.hi := rfl
@[simp] theorem sub_lo (I J : Interval p) : (I - J).lo = I.lo - J.hi := rfl
@[simp] theorem sub_hi (I J : Interval p) : (I - J).hi = I.hi - J.lo := rfl

/-- Minimum of the four corner products.  This is public so downstream raw
certificate checkers can kernel-reduce interval products. -/
def mulLower {α : Type*} [LinearOrder α] [Mul α]
    (a b c d : α) : α :=
  min (a * c) (min (a * d) (min (b * c) (b * d)))

/-- Maximum of the four corner products.  This is public so downstream raw
certificate checkers can kernel-reduce interval products. -/
def mulUpper {α : Type*} [LinearOrder α] [Mul α]
    (a b c d : α) : α :=
  max (a * c) (max (a * d) (max (b * c) (b * d)))

private theorem mul_mem_bounds {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    mulLower a b c d ≤ x * y ∧ x * y ≤ mulUpper a b c d := by
  rcases hx with ⟨hax, hxb⟩
  rcases hy with ⟨hcy, hyd⟩
  rcases (hax.trans hxb).lt_or_eq with hab | hab
  · rcases (hcy.trans hyd).lt_or_eq with hcd | hcd
    · have hba : 0 < b - a := sub_pos.mpr hab
      have hdc : 0 < d - c := sub_pos.mpr hcd
      let w₁ := (b - x) * (d - y)
      let w₂ := (b - x) * (y - c)
      let w₃ := (x - a) * (d - y)
      let w₄ := (x - a) * (y - c)
      have hw₁ : 0 ≤ w₁ := mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hyd)
      have hw₂ : 0 ≤ w₂ := mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hcy)
      have hw₃ : 0 ≤ w₃ := mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hyd)
      have hw₄ : 0 ≤ w₄ := mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hcy)
      have hweights : w₁ + w₂ + w₃ + w₄ = (b - a) * (d - c) := by
        dsimp [w₁, w₂, w₃, w₄]
        ring
      have hcorners :
          a * c * w₁ + a * d * w₂ + b * c * w₃ + b * d * w₄ =
            x * y * ((b - a) * (d - c)) := by
        dsimp [w₁, w₂, w₃, w₄]
        ring
      have hscale : 0 < (b - a) * (d - c) := mul_pos hba hdc
      constructor
      · have h₁ : mulLower a b c d * w₁ ≤ a * c * w₁ :=
          mul_le_mul_of_nonneg_right (by simp [mulLower]) hw₁
        have h₂ : mulLower a b c d * w₂ ≤ a * d * w₂ :=
          mul_le_mul_of_nonneg_right (by simp [mulLower]) hw₂
        have h₃ : mulLower a b c d * w₃ ≤ b * c * w₃ :=
          mul_le_mul_of_nonneg_right (by simp [mulLower]) hw₃
        have h₄ : mulLower a b c d * w₄ ≤ b * d * w₄ :=
          mul_le_mul_of_nonneg_right (by simp [mulLower]) hw₄
        rw [← mul_le_mul_iff_of_pos_right hscale]
        calc
          mulLower a b c d * ((b - a) * (d - c)) =
              mulLower a b c d * (w₁ + w₂ + w₃ + w₄) := by rw [hweights]
          _ = mulLower a b c d * w₁ + mulLower a b c d * w₂ +
              mulLower a b c d * w₃ + mulLower a b c d * w₄ := by ring
          _ ≤ a * c * w₁ + a * d * w₂ + b * c * w₃ + b * d * w₄ :=
            add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
          _ = x * y * ((b - a) * (d - c)) := hcorners
      · have h₁ : a * c * w₁ ≤ mulUpper a b c d * w₁ :=
          mul_le_mul_of_nonneg_right (by simp [mulUpper]) hw₁
        have h₂ : a * d * w₂ ≤ mulUpper a b c d * w₂ :=
          mul_le_mul_of_nonneg_right (by simp [mulUpper]) hw₂
        have h₃ : b * c * w₃ ≤ mulUpper a b c d * w₃ :=
          mul_le_mul_of_nonneg_right (by simp [mulUpper]) hw₃
        have h₄ : b * d * w₄ ≤ mulUpper a b c d * w₄ :=
          mul_le_mul_of_nonneg_right (by simp [mulUpper]) hw₄
        rw [← mul_le_mul_iff_of_pos_right hscale]
        calc
          x * y * ((b - a) * (d - c)) =
              a * c * w₁ + a * d * w₂ + b * c * w₃ + b * d * w₄ := hcorners.symm
          _ ≤ mulUpper a b c d * w₁ + mulUpper a b c d * w₂ +
              mulUpper a b c d * w₃ + mulUpper a b c d * w₄ :=
            add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
          _ = mulUpper a b c d * (w₁ + w₂ + w₃ + w₄) := by ring
          _ = mulUpper a b c d * ((b - a) * (d - c)) := by rw [hweights]
    · have hy' : y = c := le_antisymm (hcd ▸ hyd) hcy
      subst y
      subst d
      rcases le_total 0 c with hc | hc
      · constructor
        · exact (show mulLower a b c c ≤ a * c by simp [mulLower]).trans <|
            mul_le_mul_of_nonneg_right hax hc
        · exact (mul_le_mul_of_nonneg_right hxb hc).trans <|
            (show b * c ≤ mulUpper a b c c by simp [mulUpper])
      · constructor
        · exact (show mulLower a b c c ≤ b * c by simp [mulLower]).trans <|
            mul_le_mul_of_nonpos_right hxb hc
        · exact (mul_le_mul_of_nonpos_right hax hc).trans <|
            (show a * c ≤ mulUpper a b c c by simp [mulUpper])
  · have hx' : x = a := le_antisymm (hab ▸ hxb) hax
    subst x
    subst b
    rcases le_total 0 a with ha | ha
    · constructor
      · exact (show mulLower a a c d ≤ a * c by simp [mulLower]).trans <|
          mul_le_mul_of_nonneg_left hcy ha
      · exact (mul_le_mul_of_nonneg_left hyd ha).trans <|
          (show a * d ≤ mulUpper a a c d by simp [mulUpper])
    · constructor
      · exact (show mulLower a a c d ≤ a * d by simp [mulLower]).trans <|
          mul_le_mul_of_nonpos_left hyd ha
      · exact (mul_le_mul_of_nonpos_left hcy ha).trans <|
          (show a * c ≤ mulUpper a a c d by simp [mulUpper])

/-- Outward-rounded interval multiplication using only integer arithmetic. -/
def mul (I J : Interval p) : Interval p :=
  ⟨Dyadic.floorDiv p (mulLower I.lo I.hi J.lo J.hi),
    Dyadic.ceilDiv p (mulUpper I.lo I.hi J.lo J.hi)⟩

instance instMulInterval : Mul (Interval p) := ⟨mul⟩

@[simp] theorem mul_lo (I J : Interval p) :
    (I * J).lo = Dyadic.floorDiv p (mulLower I.lo I.hi J.lo J.hi) := rfl

@[simp] theorem mul_hi (I J : Interval p) :
    (I * J).hi = Dyadic.ceilDiv p (mulUpper I.lo I.hi J.lo J.hi) := rfl

theorem contains_enclose {p : ℕ} {lower upper : ℚ} {x : ℝ}
    (h : (lower : ℝ) ≤ x ∧ x ≤ (upper : ℝ)) :
    Contains (enclose p lower upper) x := by
  exact ⟨(Dyadic.roundDown_spec_real p lower).trans h.1,
    h.2.trans (Dyadic.roundUp_spec_real p upper)⟩

theorem contains_ofRat (p : ℕ) (x : ℚ) :
    Contains (ofRat p x) x :=
  contains_enclose ⟨le_rfl, le_rfl⟩

theorem contains_add {I J : Interval p} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I + J).Contains (x + y) := by
  change Contains (add I J) (x + y)
  exact ⟨by
      simp only [add, Dyadic.toReal_add]
      exact add_le_add hx.1 hy.1,
    by
      simp only [add, Dyadic.toReal_add]
      exact add_le_add hx.2 hy.2⟩

theorem contains_neg {I : Interval p} {x : ℝ} (hx : I.Contains x) :
    (-I).Contains (-x) := by
  change Contains (neg I) (-x)
  exact ⟨by
      simp only [neg, Dyadic.toReal_neg]
      exact neg_le_neg hx.2,
    by
      simp only [neg, Dyadic.toReal_neg]
      exact neg_le_neg hx.1⟩

theorem contains_absHull {I : Interval p} {x : ℝ} (hx : I.Contains x) :
    I.absHull.Contains |x| := by
  constructor
  · rw [absHull_lo, Dyadic.toReal_zero]
    exact abs_nonneg x
  · have hlo : Dyadic.toReal p (-I.lo) ≤
        Dyadic.toReal p (max (-I.lo) I.hi) :=
      Dyadic.toReal_mono (le_max_left _ _)
    have hhi : Dyadic.toReal p I.hi ≤
        Dyadic.toReal p (max (-I.lo) I.hi) :=
      Dyadic.toReal_mono (le_max_right _ _)
    rw [abs_le]
    constructor
    · calc
        -Dyadic.toReal p (max (-I.lo) I.hi) ≤
            -Dyadic.toReal p (-I.lo) := neg_le_neg hlo
        _ = Dyadic.toReal p I.lo := by simp [Dyadic.toReal_neg]
        _ ≤ x := hx.1
    · exact hx.2.trans hhi

theorem contains_sub {I J : Interval p} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I - J).Contains (x - y) := by
  change Contains (add I (neg J)) (x - y)
  have h := contains_add hx (contains_neg hy)
  change Contains (add I (neg J)) (x + -y) at h
  simpa [sub_eq_add_neg] using h

private theorem mulLower_toReal (p : ℕ) (a b c d : ℤ) :
    mulLower (Dyadic.toReal p a) (Dyadic.toReal p b)
        (Dyadic.toReal p c) (Dyadic.toReal p d) =
      ((mulLower a b c d : ℤ) : ℝ) / (Dyadic.scale p : ℝ) ^ 2 := by
  have hs : (0 : ℝ) ≤ (Dyadic.scale p : ℝ) ^ 2 := sq_nonneg _
  simp only [mulLower, Dyadic.toReal, Int.cast_min, Int.cast_mul]
  rw [show (a : ℝ) / Dyadic.scale p * ((c : ℝ) / Dyadic.scale p) =
      ((a : ℝ) * c) / (Dyadic.scale p : ℝ) ^ 2 by ring]
  rw [show (a : ℝ) / Dyadic.scale p * ((d : ℝ) / Dyadic.scale p) =
      ((a : ℝ) * d) / (Dyadic.scale p : ℝ) ^ 2 by ring]
  rw [show (b : ℝ) / Dyadic.scale p * ((c : ℝ) / Dyadic.scale p) =
      ((b : ℝ) * c) / (Dyadic.scale p : ℝ) ^ 2 by ring]
  rw [show (b : ℝ) / Dyadic.scale p * ((d : ℝ) / Dyadic.scale p) =
      ((b : ℝ) * d) / (Dyadic.scale p : ℝ) ^ 2 by ring]
  rw [min_div_div_right hs, min_div_div_right hs, min_div_div_right hs]

private theorem mulUpper_toReal (p : ℕ) (a b c d : ℤ) :
    mulUpper (Dyadic.toReal p a) (Dyadic.toReal p b)
        (Dyadic.toReal p c) (Dyadic.toReal p d) =
      ((mulUpper a b c d : ℤ) : ℝ) / (Dyadic.scale p : ℝ) ^ 2 := by
  have hs : (0 : ℝ) ≤ (Dyadic.scale p : ℝ) ^ 2 := sq_nonneg _
  simp only [mulUpper, Dyadic.toReal, Int.cast_max, Int.cast_mul]
  rw [show (a : ℝ) / Dyadic.scale p * ((c : ℝ) / Dyadic.scale p) =
      ((a : ℝ) * c) / (Dyadic.scale p : ℝ) ^ 2 by ring]
  rw [show (a : ℝ) / Dyadic.scale p * ((d : ℝ) / Dyadic.scale p) =
      ((a : ℝ) * d) / (Dyadic.scale p : ℝ) ^ 2 by ring]
  rw [show (b : ℝ) / Dyadic.scale p * ((c : ℝ) / Dyadic.scale p) =
      ((b : ℝ) * c) / (Dyadic.scale p : ℝ) ^ 2 by ring]
  rw [show (b : ℝ) / Dyadic.scale p * ((d : ℝ) / Dyadic.scale p) =
      ((b : ℝ) * d) / (Dyadic.scale p : ℝ) ^ 2 by ring]
  rw [max_div_div_right hs, max_div_div_right hs, max_div_div_right hs]

theorem contains_mul {I J : Interval p} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I * J).Contains (x * y) := by
  change Contains (mul I J) (x * y)
  have hbounds := mul_mem_bounds hx hy
  rw [mulLower_toReal, mulUpper_toReal] at hbounds
  exact ⟨(Dyadic.floorDiv_spec_real p _).trans hbounds.1,
    hbounds.2.trans (Dyadic.ceilDiv_spec_real p _)⟩

/--
The product of decoded upper endpoints is below the decoded upper endpoint
of interval multiplication.  This upper-only form does not require either
input interval to be valid.
-/
theorem upperRat_mul_upperRat_le (I J : Interval p) :
    (I.upperRat : ℝ) * (J.upperRat : ℝ) ≤
      ((I * J).upperRat : ℝ) := by
  have hcorner :
      Dyadic.toReal p I.hi * Dyadic.toReal p J.hi ≤
        mulUpper (Dyadic.toReal p I.lo) (Dyadic.toReal p I.hi)
          (Dyadic.toReal p J.lo) (Dyadic.toReal p J.hi) := by
    simp only [mulUpper]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hround :
      mulUpper (Dyadic.toReal p I.lo) (Dyadic.toReal p I.hi)
          (Dyadic.toReal p J.lo) (Dyadic.toReal p J.hi) ≤
        Dyadic.toReal p (I * J).hi := by
    change
      mulUpper (Dyadic.toReal p I.lo) (Dyadic.toReal p I.hi)
          (Dyadic.toReal p J.lo) (Dyadic.toReal p J.hi) ≤
        Dyadic.toReal p
          (Dyadic.ceilDiv p (mulUpper I.lo I.hi J.lo J.hi))
    rw [mulUpper_toReal]
    exact Dyadic.ceilDiv_spec_real p _
  simpa only [Interval.upperRat, Dyadic.cast_toRat] using
    hcorner.trans hround

/-- Outward-rounded reciprocal. Soundness requires an interval of one sign. -/
def reciprocal (I : Interval p) : Interval p :=
  let scaleSquared : ℤ := (Dyadic.scale p : ℤ) ^ 2
  ⟨Dyadic.floorDivBy scaleSquared I.hi,
    Dyadic.ceilDivBy scaleSquared I.lo⟩

/--
Reciprocal enclosure for a strictly positive interval.  The sign condition is
stated on raw data so a reflected checker can discharge it by computation.
-/
theorem contains_reciprocal_of_pos {I : Interval p} {x : ℝ}
    (hpos : 0 < I.lo) (hx : I.Contains x) :
    I.reciprocal.Contains x⁻¹ := by
  have hvalid : I.Valid := by
    have h : Dyadic.toReal p I.lo ≤ Dyadic.toReal p I.hi :=
      hx.1.trans hx.2
    have hs : (0 : ℝ) < Dyadic.scale p := by
      exact_mod_cast Dyadic.scale_pos p
    rw [Dyadic.toReal, Dyadic.toReal,
      div_le_div_iff_of_pos_right hs] at h
    exact_mod_cast h
  have hhiRaw : 0 < I.hi := hpos.trans_le hvalid
  have hlo : (0 : ℝ) < Dyadic.toReal p I.lo := by
    exact div_pos (by exact_mod_cast hpos) (by exact_mod_cast Dyadic.scale_pos p)
  have hxpos : 0 < x := hlo.trans_le hx.1
  have hhi : 0 < Dyadic.toReal p I.hi := hxpos.trans_le hx.2
  have hs : (0 : ℝ) < Dyadic.scale p := by
    exact_mod_cast Dyadic.scale_pos p
  have hlower :
      Dyadic.toReal p
          (Dyadic.floorDivBy ((Dyadic.scale p : ℤ) ^ 2) I.hi) ≤
        (Dyadic.toReal p I.hi)⁻¹ := by
    rw [Dyadic.toReal]
    calc
      (Dyadic.floorDivBy ((Dyadic.scale p : ℤ) ^ 2) I.hi : ℝ) /
          Dyadic.scale p ≤
          (((Dyadic.scale p : ℤ) ^ 2 : ℤ) : ℝ) /
            (I.hi : ℝ) / Dyadic.scale p :=
        div_le_div_of_nonneg_right
          (Dyadic.floorDivBy_spec_real _ hhiRaw) hs.le
      _ = (Dyadic.toReal p I.hi)⁻¹ := by
        rw [Dyadic.toReal]
        norm_num
        field_simp
  have hupper :
      (Dyadic.toReal p I.lo)⁻¹ ≤
        Dyadic.toReal p
          (Dyadic.ceilDivBy ((Dyadic.scale p : ℤ) ^ 2) I.lo) := by
    rw [Dyadic.toReal]
    calc
      ((I.lo : ℝ) / Dyadic.scale p)⁻¹ =
          (((Dyadic.scale p : ℤ) ^ 2 : ℤ) : ℝ) /
            (I.lo : ℝ) / Dyadic.scale p := by
        norm_num
        field_simp
      _ ≤ (Dyadic.ceilDivBy ((Dyadic.scale p : ℤ) ^ 2) I.lo : ℝ) /
          Dyadic.scale p :=
        div_le_div_of_nonneg_right
          (Dyadic.ceilDivBy_spec_real _ hpos) hs.le
  change Contains
    ⟨Dyadic.floorDivBy ((Dyadic.scale p : ℤ) ^ 2) I.hi,
      Dyadic.ceilDivBy ((Dyadic.scale p : ℤ) ^ 2) I.lo⟩ x⁻¹
  exact ⟨hlower.trans ((inv_le_inv₀ hhi hxpos).mpr hx.2),
    ((inv_le_inv₀ hxpos hlo).mpr hx.1).trans hupper⟩

/--
Outward-rounded squaring.  In the only case where ordinary interval
multiplication would introduce a negative lower endpoint, replace it by the
sharp lower bound zero.
-/
def square (I : Interval p) : Interval p :=
  if I.lo ≤ 0 ∧ 0 ≤ I.hi then ⟨0, (I * I).hi⟩ else I * I

/-- Squaring an ordered interval with nonnegative lower endpoint preserves a
nonnegative raw lower endpoint. -/
theorem square_lo_nonneg_of_lo_nonneg {I : Interval p}
    (hvalid : I.Valid) (hlo : 0 ≤ I.lo) : 0 ≤ I.square.lo := by
  by_cases hz : I.lo = 0
  · rw [square, if_pos ⟨by omega, by simpa [Valid, hz] using hvalid⟩]
  · have hloPos : 0 < I.lo := lt_of_le_of_ne hlo (Ne.symm hz)
    rw [square, if_neg (by omega)]
    change 0 ≤ Dyadic.floorDiv p (mulLower I.lo I.hi I.lo I.hi)
    unfold Dyadic.floorDiv
    apply Int.ediv_nonneg
    · simp only [mulLower]
      have hhi : 0 ≤ I.hi := hlo.trans hvalid
      positivity
    · exact_mod_cast (Dyadic.scale_pos p).le

theorem contains_square {I : Interval p} {x : ℝ} (hx : I.Contains x) :
    I.square.Contains (x ^ 2) := by
  by_cases hcrosses : I.lo ≤ 0 ∧ 0 ≤ I.hi
  · have hmul := contains_mul hx hx
    rw [square, if_pos hcrosses]
    change Contains ⟨0, (I * I).hi⟩ (x ^ 2)
    exact ⟨by
        simpa [Dyadic.toReal_zero] using sq_nonneg x,
      by simpa [pow_two] using hmul.2⟩
  · simpa [square, hcrosses, pow_two] using contains_mul hx hx

/-- Repeated squaring, used for powers whose exponent is a power of two. -/
def squareN (I : Interval p) : ℕ → Interval p
  | 0 => I
  | n + 1 => (squareN I n).square

/-- Repeated squaring on an arbitrary monoid-like carrier. -/
def iterSquare {α : Type*} [Mul α] (x : α) : ℕ → α
  | 0 => x
  | n + 1 => iterSquare x n * iterSquare x n

theorem contains_squareN {I : Interval p} {x : ℝ} (hx : I.Contains x) (n : ℕ) :
    (I.squareN n).Contains (iterSquare x n) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      simpa [squareN, iterSquare, pow_two] using contains_square ih

theorem iterSquare_eq_pow_two_pow (x : ℝ) (n : ℕ) :
    iterSquare x n = x ^ (2 ^ n) := by
  induction n with
  | zero => simp [iterSquare]
  | succ n ih =>
      rw [iterSquare, ih, ← pow_add]
      congr 1
      omega

theorem valid_of_contains {I : Interval p} {x : ℝ} (hx : I.Contains x) :
    I.Valid := by
  have h : Dyadic.toReal p I.lo ≤ Dyadic.toReal p I.hi := hx.1.trans hx.2
  have hs : (0 : ℝ) < Dyadic.scale p := by
    exact_mod_cast Dyadic.scale_pos p
  rw [Dyadic.toReal, Dyadic.toReal, div_le_div_iff_of_pos_right hs] at h
  exact_mod_cast h

end Interval
end CertifiedProjections
