/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Regimes.Dense.ScalarP3
import CertifiedProjections.Arithmetic.Interval.Reflection
import Mathlib.Tactic.NormNum

/-!
# Kernel-checked alternate dense `p = 3` endpoint

This module is the executable numerical boundary for the independent
polynomial producer in `DenseScalarP3`.  It uses exact dyadic intervals and
the transparent exponential enclosure from `CertifiedProjections.Arithmetic.Transcendental.Exponential.Exp`.
The lower endpoint of each negative exponential is obtained by reciprocating
an upper enclosure for the corresponding positive exponential; this is
necessary because the majorant has negative coefficients at moments 3 and 5.
-/

noncomputable section

namespace CertifiedProjections
namespace DenseScalar

/-- Dyadic precision used by the alternate dense endpoint certificate. -/
def p3CertificatePrecision : ℕ := 32

/-- Repeated-squaring depth used by the alternate dense endpoint certificate. -/
def p3CertificateSquarings : ℕ := 12

private def p3Rat (x : ℚ) : Interval p3CertificatePrecision :=
  Interval.ofRat p3CertificatePrecision x

private def p3ExpNegInterval (x : ℚ) : Interval p3CertificatePrecision :=
  ⟨((Exp.posBase p3CertificatePrecision x p3CertificateSquarings).squareN
      p3CertificateSquarings).reciprocal.lo,
    (Exp.negUpper p3CertificatePrecision x p3CertificateSquarings).hi⟩

private theorem p3ExpNegInterval_contains {x : ℚ}
    (hx : 0 ≤ x) (hupper : x < (2 ^ p3CertificateSquarings : ℕ))
    (hbase : 0 < (Interval.ofRat p3CertificatePrecision
      (1 - x / (2 ^ p3CertificateSquarings : ℕ))).lo)
    (hraw_pos : 0 <
      ((Exp.posBase p3CertificatePrecision x p3CertificateSquarings).squareN
        p3CertificateSquarings).lo) :
    (p3ExpNegInterval x).Contains (Real.exp (-(x : ℝ))) := by
  let argument : ℚ := x / (2 ^ p3CertificateSquarings : ℕ)
  have hdiff :
      (Interval.ofRat p3CertificatePrecision (1 - argument)).Contains
        (1 - (argument : ℝ)) := by
    simpa [argument] using
      Interval.contains_ofRat p3CertificatePrecision (1 - argument)
  have hbase_contains :
      (Exp.posBase p3CertificatePrecision x p3CertificateSquarings).Contains
        ((1 - (argument : ℝ))⁻¹) := by
    unfold Exp.posBase
    apply Interval.contains_reciprocal_of_pos
    · simpa [argument] using hbase
    · exact hdiff
  have hpow := Interval.contains_squareN hbase_contains p3CertificateSquarings
  have harg_lt : (argument : ℝ) < 1 := by
    have hden : (0 : ℝ) < (2 ^ p3CertificateSquarings : ℕ) := by positivity
    have hxreal : (x : ℝ) < (2 ^ p3CertificateSquarings : ℕ) := by
      exact_mod_cast hupper
    have h := (div_lt_one hden).2 hxreal
    simpa [argument] using h
  have hbase_exp :
      Real.exp (argument : ℝ) ≤ (1 - (argument : ℝ))⁻¹ := by
    calc
      Real.exp (argument : ℝ) =
          (Real.exp (-(argument : ℝ)))⁻¹ := by
        simpa using Real.exp_neg (-(argument : ℝ))
      _ ≤ (1 - (argument : ℝ))⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (sub_pos.mpr harg_lt)).mpr <|
          by linarith [Real.add_one_le_exp (-(argument : ℝ))]
  have hupper_real :
      Real.exp (x : ℝ) ≤
        Interval.iterSquare ((1 - (argument : ℝ))⁻¹)
          p3CertificateSquarings := by
    rw [Interval.iterSquare_eq_pow_two_pow]
    have harg_eq : (argument : ℝ) =
        (x : ℝ) / (2 ^ p3CertificateSquarings : ℕ) := by
      simp [argument]
    calc
      Real.exp (x : ℝ) =
          Real.exp ((2 ^ p3CertificateSquarings : ℕ) * (argument : ℝ)) := by
            congr 1
            rw [harg_eq]
            field_simp
      _ = Real.exp (argument : ℝ) ^
          (2 ^ p3CertificateSquarings : ℕ) := by
            rw [Real.exp_nat_mul]
      _ ≤ ((1 - (argument : ℝ))⁻¹) ^
          (2 ^ p3CertificateSquarings : ℕ) := by
        exact pow_le_pow_left₀ (Real.exp_nonneg _) hbase_exp _
  have hrecip := Interval.contains_reciprocal_of_pos hraw_pos hpow
  have hinv :
      (Interval.iterSquare ((1 - (argument : ℝ))⁻¹)
          p3CertificateSquarings)⁻¹ ≤
        Real.exp (-(x : ℝ)) := by
    have harg_pos : 0 < 1 - (argument : ℝ) := sub_pos.mpr harg_lt
    have hUpos : 0 < Interval.iterSquare
        ((1 - (argument : ℝ))⁻¹) p3CertificateSquarings := by
      rw [Interval.iterSquare_eq_pow_two_pow]
      positivity
    rw [Real.exp_neg]
    exact (inv_le_inv₀ hUpos (Real.exp_pos _)).mpr hupper_real
  have hupper_neg := Exp.negUpper_contains
    (p := p3CertificatePrecision) (k := p3CertificateSquarings)
    (x := x) hx
  change (p3ExpNegInterval x).Contains (Real.exp (-(x : ℝ)))
  exact ⟨hrecip.1.trans hinv, by simpa [p3ExpNegInterval] using hupper_neg.2⟩

set_option maxHeartbeats 10000000 in
-- The reflected endpoint arithmetic expands six 12-round exact dyadic checks.
private theorem p3_exp_neg_13_6_contains :
    (p3ExpNegInterval (13 / 6)).Contains (Real.exp (-(13 : ℝ) / 6)) := by
  have h := p3ExpNegInterval_contains (x := (13 / 6 : ℚ))
    (by norm_num) (by norm_num [p3CertificateSquarings])
    (by
      change 0 < Dyadic.roundDown p3CertificatePrecision
        (1 - (13 / 6 : ℚ) / (2 ^ p3CertificateSquarings : ℕ))
      apply Dyadic.roundDown_pos
      norm_num [p3CertificatePrecision, p3CertificateSquarings, Dyadic.scale])
    (by decide +kernel)
  convert h using 1; norm_num

set_option maxHeartbeats 10000000 in
-- The reflected endpoint arithmetic expands six 12-round exact dyadic checks.
private theorem p3_exp_neg_26_3_contains :
    (p3ExpNegInterval (26 / 3)).Contains (Real.exp (-(26 : ℝ) / 3)) := by
  have h := p3ExpNegInterval_contains (x := (26 / 3 : ℚ))
    (by norm_num) (by norm_num [p3CertificateSquarings])
    (by
      change 0 < Dyadic.roundDown p3CertificatePrecision
        (1 - (26 / 3 : ℚ) / (2 ^ p3CertificateSquarings : ℕ))
      apply Dyadic.roundDown_pos
      norm_num [p3CertificatePrecision, p3CertificateSquarings, Dyadic.scale])
    (by decide +kernel)
  convert h using 1; norm_num

set_option maxHeartbeats 10000000 in
-- The reflected endpoint arithmetic expands six 12-round exact dyadic checks.
private theorem p3_exp_neg_39_2_contains :
    (p3ExpNegInterval (39 / 2)).Contains (Real.exp (-(39 : ℝ) / 2)) := by
  have h := p3ExpNegInterval_contains (x := (39 / 2 : ℚ))
    (by norm_num) (by norm_num [p3CertificateSquarings])
    (by
      change 0 < Dyadic.roundDown p3CertificatePrecision
        (1 - (39 / 2 : ℚ) / (2 ^ p3CertificateSquarings : ℕ))
      apply Dyadic.roundDown_pos
      norm_num [p3CertificatePrecision, p3CertificateSquarings, Dyadic.scale])
    (by decide +kernel)
  convert h using 1; norm_num

set_option maxHeartbeats 10000000 in
-- The reflected endpoint arithmetic expands six 12-round exact dyadic checks.
private theorem p3_exp_neg_104_3_contains :
    (p3ExpNegInterval (104 / 3)).Contains (Real.exp (-(104 : ℝ) / 3)) := by
  have h := p3ExpNegInterval_contains (x := (104 / 3 : ℚ))
    (by norm_num) (by norm_num [p3CertificateSquarings])
    (by
      change 0 < Dyadic.roundDown p3CertificatePrecision
        (1 - (104 / 3 : ℚ) / (2 ^ p3CertificateSquarings : ℕ))
      apply Dyadic.roundDown_pos
      norm_num [p3CertificatePrecision, p3CertificateSquarings, Dyadic.scale])
    (by decide +kernel)
  convert h using 1; norm_num

set_option maxHeartbeats 10000000 in
-- The reflected endpoint arithmetic expands six 12-round exact dyadic checks.
private theorem p3_exp_neg_325_6_contains :
    (p3ExpNegInterval (325 / 6)).Contains (Real.exp (-(325 : ℝ) / 6)) := by
  have h := p3ExpNegInterval_contains (x := (325 / 6 : ℚ))
    (by norm_num) (by norm_num [p3CertificateSquarings])
    (by
      change 0 < Dyadic.roundDown p3CertificatePrecision
        (1 - (325 / 6 : ℚ) / (2 ^ p3CertificateSquarings : ℕ))
      apply Dyadic.roundDown_pos
      norm_num [p3CertificatePrecision, p3CertificateSquarings, Dyadic.scale])
    (by decide +kernel)
  convert h using 1; norm_num

set_option maxHeartbeats 10000000 in
-- The reflected endpoint arithmetic expands six 12-round exact dyadic checks.
private theorem p3_exp_neg_78_contains :
    (p3ExpNegInterval 78).Contains (Real.exp (-78)) := by
  have h := p3ExpNegInterval_contains (x := (78 : ℚ))
    (by norm_num) (by norm_num [p3CertificateSquarings])
    (by
      change 0 < Dyadic.roundDown p3CertificatePrecision
        (1 - (78 : ℚ) / (2 ^ p3CertificateSquarings : ℕ))
      apply Dyadic.roundDown_pos
      norm_num [p3CertificatePrecision, p3CertificateSquarings, Dyadic.scale])
    (by decide +kernel)
  convert h using 1; norm_num

private def p3MomentOne : Interval p3CertificatePrecision :=
  p3Rat (1 / 2) + p3Rat (1 / 2) * p3ExpNegInterval (13 / 6)

private def p3MomentTwo : Interval p3CertificatePrecision :=
  p3Rat (3 / 8) + p3Rat (1 / 2) * p3ExpNegInterval (13 / 6) +
    p3Rat (1 / 8) * p3ExpNegInterval (26 / 3)

private def p3MomentThree : Interval p3CertificatePrecision :=
  p3Rat (10 / 32) + p3Rat (15 / 32) * p3ExpNegInterval (13 / 6) +
    p3Rat (6 / 32) * p3ExpNegInterval (26 / 3) +
      p3Rat (1 / 32) * p3ExpNegInterval (39 / 2)

private def p3MomentFour : Interval p3CertificatePrecision :=
  p3Rat (35 / 128) + p3Rat (56 / 128) * p3ExpNegInterval (13 / 6) +
    p3Rat (28 / 128) * p3ExpNegInterval (26 / 3) +
      p3Rat (8 / 128) * p3ExpNegInterval (39 / 2) +
        p3Rat (1 / 128) * p3ExpNegInterval (104 / 3)

private def p3MomentFive : Interval p3CertificatePrecision :=
  p3Rat (126 / 512) + p3Rat (210 / 512) * p3ExpNegInterval (13 / 6) +
    p3Rat (120 / 512) * p3ExpNegInterval (26 / 3) +
      p3Rat (45 / 512) * p3ExpNegInterval (39 / 2) +
        p3Rat (10 / 512) * p3ExpNegInterval (104 / 3) +
          p3Rat (1 / 512) * p3ExpNegInterval (325 / 6)

private def p3MomentSix : Interval p3CertificatePrecision :=
  p3Rat (462 / 2048) + p3Rat (792 / 2048) * p3ExpNegInterval (13 / 6) +
    p3Rat (495 / 2048) * p3ExpNegInterval (26 / 3) +
      p3Rat (220 / 2048) * p3ExpNegInterval (39 / 2) +
        p3Rat (66 / 2048) * p3ExpNegInterval (104 / 3) +
          p3Rat (12 / 2048) * p3ExpNegInterval (325 / 6) +
            p3Rat (1 / 2048) * p3ExpNegInterval 78

/-- The exact alternate majorant endpoint consumed by the numeric certificate. -/
def p3AlternateEndpoint : ℝ :=
  (14283 : ℝ) / 85750 * p3EvenMoment 1 +
    (153323 / 85750 : ℝ) * p3EvenMoment 2 -
      (2769016 / 1157625 : ℝ) * p3EvenMoment 3 +
        (1040968 / 385875 : ℝ) * p3EvenMoment 4 -
          (93952 / 55125 : ℝ) * p3EvenMoment 5 +
            (514048 / 1157625 : ℝ) * p3EvenMoment 6

/-- Exact dyadic enclosure of the alternate dense endpoint. -/
def p3AlternateUpperInterval : Interval p3CertificatePrecision :=
  p3Rat (14283 / 85750) * p3MomentOne +
    p3Rat (153323 / 85750) * p3MomentTwo -
      p3Rat (2769016 / 1157625) * p3MomentThree +
        p3Rat (1040968 / 385875) * p3MomentFour -
          p3Rat (93952 / 55125) * p3MomentFive +
            p3Rat (514048 / 1157625) * p3MomentSix

/-- Executable strict check for the alternate endpoint `< 971/2000`. -/
def p3AlternateCheck : Bool :=
  Interval.upperLTCheck p3AlternateUpperInterval (971 / 2000)

/-- The alternate endpoint check closes by kernel reduction. -/
theorem p3AlternateCheck_eq_true : p3AlternateCheck = true := by
  decide +kernel

private theorem p3MomentOne_contains :
    p3MomentOne.Contains (p3EvenMoment 1) := by
  have he := p3_exp_neg_13_6_contains
  have h0 := Interval.contains_ofRat p3CertificatePrecision (1 / 2 : ℚ)
  have hterm := Interval.contains_mul h0 he
  rw [p3_even_moment_one]
  simpa [p3MomentOne, p3Rat] using
    Interval.contains_add h0 hterm

private theorem p3MomentTwo_contains :
    p3MomentTwo.Contains (p3EvenMoment 2) := by
  have he13 := p3_exp_neg_13_6_contains
  have he26 := p3_exp_neg_26_3_contains
  have h0 := Interval.contains_ofRat p3CertificatePrecision (3 / 8 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (1 / 2 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (1 / 8 : ℚ)) he26
  have hsum := Interval.contains_add h0 h13
  rw [p3_even_moment_two]
  simpa [p3MomentTwo, p3Rat] using Interval.contains_add hsum h26

private theorem p3MomentThree_contains :
    p3MomentThree.Contains (p3EvenMoment 3) := by
  have he13 := p3_exp_neg_13_6_contains
  have he26 := p3_exp_neg_26_3_contains
  have he39 := p3_exp_neg_39_2_contains
  have h0 := Interval.contains_ofRat p3CertificatePrecision (10 / 32 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (15 / 32 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (6 / 32 : ℚ)) he26
  have h39 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (1 / 32 : ℚ)) he39
  have hsum := Interval.contains_add (Interval.contains_add h0 h13) h26
  rw [p3_even_moment_three]
  simpa [p3MomentThree, p3Rat] using Interval.contains_add hsum h39

private theorem p3MomentFour_contains :
    p3MomentFour.Contains (p3EvenMoment 4) := by
  have he13 := p3_exp_neg_13_6_contains
  have he26 := p3_exp_neg_26_3_contains
  have he39 := p3_exp_neg_39_2_contains
  have he104 := p3_exp_neg_104_3_contains
  have h0 := Interval.contains_ofRat p3CertificatePrecision (35 / 128 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (56 / 128 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (28 / 128 : ℚ)) he26
  have h39 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (8 / 128 : ℚ)) he39
  have h104 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (1 / 128 : ℚ)) he104
  have hsum0 := Interval.contains_add (Interval.contains_add h0 h13) h26
  have hsum1 := Interval.contains_add hsum0 h39
  rw [p3_even_moment_four]
  simpa [p3MomentFour, p3Rat] using Interval.contains_add hsum1 h104

private theorem p3MomentFive_contains :
    p3MomentFive.Contains (p3EvenMoment 5) := by
  have he13 := p3_exp_neg_13_6_contains
  have he26 := p3_exp_neg_26_3_contains
  have he39 := p3_exp_neg_39_2_contains
  have he104 := p3_exp_neg_104_3_contains
  have he325 := p3_exp_neg_325_6_contains
  have h0 := Interval.contains_ofRat p3CertificatePrecision (126 / 512 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (210 / 512 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (120 / 512 : ℚ)) he26
  have h39 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (45 / 512 : ℚ)) he39
  have h104 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (10 / 512 : ℚ)) he104
  have h325 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (1 / 512 : ℚ)) he325
  have hsum0 := Interval.contains_add (Interval.contains_add h0 h13) h26
  have hsum1 := Interval.contains_add hsum0 h39
  have hsum2 := Interval.contains_add hsum1 h104
  rw [p3_even_moment_five]
  simpa [p3MomentFive, p3Rat] using Interval.contains_add hsum2 h325

private theorem p3MomentSix_contains :
    p3MomentSix.Contains (p3EvenMoment 6) := by
  have he13 := p3_exp_neg_13_6_contains
  have he26 := p3_exp_neg_26_3_contains
  have he39 := p3_exp_neg_39_2_contains
  have he104 := p3_exp_neg_104_3_contains
  have he325 := p3_exp_neg_325_6_contains
  have he78 := p3_exp_neg_78_contains
  have h0 := Interval.contains_ofRat p3CertificatePrecision (462 / 2048 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (792 / 2048 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (495 / 2048 : ℚ)) he26
  have h39 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (220 / 2048 : ℚ)) he39
  have h104 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (66 / 2048 : ℚ)) he104
  have h325 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (12 / 2048 : ℚ)) he325
  have h78 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (1 / 2048 : ℚ)) he78
  have hsum0 := Interval.contains_add (Interval.contains_add h0 h13) h26
  have hsum1 := Interval.contains_add hsum0 h39
  have hsum2 := Interval.contains_add hsum1 h104
  have hsum3 := Interval.contains_add hsum2 h325
  rw [p3_even_moment_six]
  simpa [p3MomentSix, p3Rat] using Interval.contains_add hsum3 h78

/-- The interval encloses the exact six-moment alternate endpoint. -/
theorem p3AlternateUpperInterval_contains :
    p3AlternateUpperInterval.Contains p3AlternateEndpoint := by
  have h1 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (14283 / 85750 : ℚ))
    p3MomentOne_contains
  have h2 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (153323 / 85750 : ℚ))
    p3MomentTwo_contains
  have h3 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (2769016 / 1157625 : ℚ))
    p3MomentThree_contains
  have h4 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (1040968 / 385875 : ℚ))
    p3MomentFour_contains
  have h5 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (93952 / 55125 : ℚ))
    p3MomentFive_contains
  have h6 := Interval.contains_mul
    (Interval.contains_ofRat p3CertificatePrecision (514048 / 1157625 : ℚ))
    p3MomentSix_contains
  have h12 := Interval.contains_add h1 h2
  have h123 := Interval.contains_sub h12 h3
  have h1234 := Interval.contains_add h123 h4
  have h12345 := Interval.contains_sub h1234 h5
  have h := Interval.contains_add h12345 h6
  simpa [p3AlternateUpperInterval, p3AlternateEndpoint, p3Rat] using h

/-- The alternate polynomial endpoint is strictly below `971/2000`. -/
theorem p3AlternateEndpoint_lt :
    p3AlternateEndpoint < (971 / 2000 : ℝ) := by
  have h := Interval.lt_of_contains_of_upperLTCheck
    p3AlternateUpperInterval_contains p3AlternateCheck_eq_true
  convert h using 1; norm_num

/-- The dense scalar `p = 3` profile satisfies the alternate target. -/
theorem sparseScalarF_13_div_4_three_lt_971_over_2000 :
    sparseScalarF (13 / 4) 3 < (971 / 2000 : ℝ) := by
  exact (sparseScalarF_13_div_4_three_le_even_majorant.trans_lt
    p3AlternateEndpoint_lt)

end DenseScalar
end CertifiedProjections
