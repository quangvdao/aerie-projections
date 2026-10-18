/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedProjections.Certificates.Families.L2Lower.Shared.Dense.Soundness.DenseScalarP3Certificate
import CertifiedProjections.Arithmetic.Interval.Reflection
import Mathlib.Tactic.NormNum

/-!
# Tight kernel-checked alternate dense `p = 3` endpoint

This module is a deliberately separate numerical boundary for the `[3,8]`
interpolation consumer.  The published alternate endpoint certificate keeps
its compact 32-bit/12-squaring budget; this consumer uses a 48-bit/32-squaring
enclosure so that the certified endpoint is tight enough for the universal
interpolation target.  Both certificates enclose the same exact endpoint.
-/

noncomputable section

namespace CertifiedProjections
namespace DenseScalar

/-- Dyadic precision used by the interpolation-only dense endpoint certificate. -/
def p3TightCertificatePrecision : ℕ := 48

/-- Repeated-squaring depth used by the interpolation-only endpoint certificate. -/
def p3TightCertificateSquarings : ℕ := 32

private def p3TightRat (x : ℚ) : Interval p3TightCertificatePrecision :=
  Interval.ofRat p3TightCertificatePrecision x

private def p3TightExpNegInterval (x : ℚ) :
    Interval p3TightCertificatePrecision :=
  ⟨((Exp.posBase p3TightCertificatePrecision x
      p3TightCertificateSquarings).squareN p3TightCertificateSquarings).reciprocal.lo,
    (Exp.negUpper p3TightCertificatePrecision x
      p3TightCertificateSquarings).hi⟩

private theorem p3TightExpNegInterval_contains {x : ℚ}
    (hx : 0 ≤ x) (hupper : x < (2 ^ p3TightCertificateSquarings : ℕ))
    (hbase : 0 < (Interval.ofRat p3TightCertificatePrecision
      (1 - x / (2 ^ p3TightCertificateSquarings : ℕ))).lo)
    (hraw_pos : 0 <
      ((Exp.posBase p3TightCertificatePrecision x
        p3TightCertificateSquarings).squareN p3TightCertificateSquarings).lo) :
    (p3TightExpNegInterval x).Contains (Real.exp (-(x : ℝ))) := by
  let argument : ℚ := x / (2 ^ p3TightCertificateSquarings : ℕ)
  have hdiff :
      (Interval.ofRat p3TightCertificatePrecision (1 - argument)).Contains
        (1 - (argument : ℝ)) := by
    simpa [argument] using
      Interval.contains_ofRat p3TightCertificatePrecision (1 - argument)
  have hbase_contains :
      (Exp.posBase p3TightCertificatePrecision x
        p3TightCertificateSquarings).Contains
        ((1 - (argument : ℝ))⁻¹) := by
    unfold Exp.posBase
    apply Interval.contains_reciprocal_of_pos
    · simpa [argument] using hbase
    · exact hdiff
  have hpow := Interval.contains_squareN hbase_contains
    p3TightCertificateSquarings
  have harg_lt : (argument : ℝ) < 1 := by
    have hden : (0 : ℝ) < (2 ^ p3TightCertificateSquarings : ℕ) := by
      positivity
    have hxreal : (x : ℝ) < (2 ^ p3TightCertificateSquarings : ℕ) := by
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
          p3TightCertificateSquarings := by
    rw [Interval.iterSquare_eq_pow_two_pow]
    have harg_eq : (argument : ℝ) =
        (x : ℝ) / (2 ^ p3TightCertificateSquarings : ℕ) := by
      simp [argument]
    calc
      Real.exp (x : ℝ) =
          Real.exp ((2 ^ p3TightCertificateSquarings : ℕ) *
            (argument : ℝ)) := by
            congr 1
            rw [harg_eq]
            field_simp
      _ = Real.exp (argument : ℝ) ^
          (2 ^ p3TightCertificateSquarings : ℕ) := by
            rw [Real.exp_nat_mul]
      _ ≤ ((1 - (argument : ℝ))⁻¹) ^
          (2 ^ p3TightCertificateSquarings : ℕ) := by
        exact pow_le_pow_left₀ (Real.exp_nonneg _) hbase_exp _
  have hrecip := Interval.contains_reciprocal_of_pos hraw_pos hpow
  have hinv :
      (Interval.iterSquare ((1 - (argument : ℝ))⁻¹)
          p3TightCertificateSquarings)⁻¹ ≤
        Real.exp (-(x : ℝ)) := by
    have harg_pos : 0 < 1 - (argument : ℝ) := sub_pos.mpr harg_lt
    have hUpos : 0 < Interval.iterSquare
        ((1 - (argument : ℝ))⁻¹) p3TightCertificateSquarings := by
      rw [Interval.iterSquare_eq_pow_two_pow]
      positivity
    rw [Real.exp_neg]
    exact (inv_le_inv₀ hUpos (Real.exp_pos _)).mpr hupper_real
  have hupper_neg := Exp.negUpper_contains
    (p := p3TightCertificatePrecision)
    (k := p3TightCertificateSquarings) (x := x) hx
  change (p3TightExpNegInterval x).Contains (Real.exp (-(x : ℝ)))
  exact ⟨hrecip.1.trans hinv, by
    simpa [p3TightExpNegInterval] using hupper_neg.2⟩

private def p3TightMomentOne : Interval p3TightCertificatePrecision :=
  p3TightRat (1 / 2) + p3TightRat (1 / 2) *
    p3TightExpNegInterval (13 / 6)

private def p3TightMomentTwo : Interval p3TightCertificatePrecision :=
  p3TightRat (3 / 8) + p3TightRat (1 / 2) *
      p3TightExpNegInterval (13 / 6) + p3TightRat (1 / 8) *
        p3TightExpNegInterval (26 / 3)

private def p3TightMomentThree : Interval p3TightCertificatePrecision :=
  p3TightRat (10 / 32) + p3TightRat (15 / 32) *
      p3TightExpNegInterval (13 / 6) + p3TightRat (6 / 32) *
        p3TightExpNegInterval (26 / 3) + p3TightRat (1 / 32) *
          p3TightExpNegInterval (39 / 2)

private def p3TightMomentFour : Interval p3TightCertificatePrecision :=
  p3TightRat (35 / 128) + p3TightRat (56 / 128) *
      p3TightExpNegInterval (13 / 6) + p3TightRat (28 / 128) *
        p3TightExpNegInterval (26 / 3) + p3TightRat (8 / 128) *
          p3TightExpNegInterval (39 / 2) + p3TightRat (1 / 128) *
            p3TightExpNegInterval (104 / 3)

private def p3TightMomentFive : Interval p3TightCertificatePrecision :=
  p3TightRat (126 / 512) + p3TightRat (210 / 512) *
      p3TightExpNegInterval (13 / 6) + p3TightRat (120 / 512) *
        p3TightExpNegInterval (26 / 3) + p3TightRat (45 / 512) *
          p3TightExpNegInterval (39 / 2) + p3TightRat (10 / 512) *
            p3TightExpNegInterval (104 / 3) + p3TightRat (1 / 512) *
              p3TightExpNegInterval (325 / 6)

private def p3TightMomentSix : Interval p3TightCertificatePrecision :=
  p3TightRat (462 / 2048) + p3TightRat (792 / 2048) *
      p3TightExpNegInterval (13 / 6) + p3TightRat (495 / 2048) *
        p3TightExpNegInterval (26 / 3) + p3TightRat (220 / 2048) *
          p3TightExpNegInterval (39 / 2) + p3TightRat (66 / 2048) *
            p3TightExpNegInterval (104 / 3) + p3TightRat (12 / 2048) *
              p3TightExpNegInterval (325 / 6) + p3TightRat (1 / 2048) *
                p3TightExpNegInterval 78

/-- Exact dyadic enclosure of the alternate endpoint for `[3,8]` interpolation. -/
def p3TightUpperInterval : Interval p3TightCertificatePrecision :=
  p3TightRat (14283 / 85750) * p3TightMomentOne +
    p3TightRat (153323 / 85750) * p3TightMomentTwo -
      p3TightRat (2769016 / 1157625) * p3TightMomentThree +
        p3TightRat (1040968 / 385875) * p3TightMomentFour -
          p3TightRat (93952 / 55125) * p3TightMomentFive +
            p3TightRat (514048 / 1157625) * p3TightMomentSix

private theorem p3TightMomentOne_contains :
    p3TightMomentOne.Contains (p3EvenMoment 1) := by
  have he := p3TightExpNegInterval_contains (x := (13 / 6 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have h0 := Interval.contains_ofRat p3TightCertificatePrecision (1 / 2 : ℚ)
  have hterm := Interval.contains_mul h0 he
  norm_num at he
  rw [p3_even_moment_one]
  convert Interval.contains_add h0 hterm using 1 <;>
    norm_num [p3TightMomentOne, p3TightRat]

private theorem p3TightMomentTwo_contains :
    p3TightMomentTwo.Contains (p3EvenMoment 2) := by
  have he13 := p3TightExpNegInterval_contains (x := (13 / 6 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he26 := p3TightExpNegInterval_contains (x := (26 / 3 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  norm_num at he13 he26
  have h0 := Interval.contains_ofRat p3TightCertificatePrecision (3 / 8 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (1 / 2 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (1 / 8 : ℚ)) he26
  rw [p3_even_moment_two]
  convert Interval.contains_add (Interval.contains_add h0 h13) h26 using 1 <;>
    norm_num [p3TightMomentTwo, p3TightRat]

private theorem p3TightMomentThree_contains :
    p3TightMomentThree.Contains (p3EvenMoment 3) := by
  have he13 := p3TightExpNegInterval_contains (x := (13 / 6 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he26 := p3TightExpNegInterval_contains (x := (26 / 3 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he39 := p3TightExpNegInterval_contains (x := (39 / 2 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  norm_num at he13 he26 he39
  have h0 := Interval.contains_ofRat p3TightCertificatePrecision (10 / 32 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (15 / 32 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (6 / 32 : ℚ)) he26
  have h39 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (1 / 32 : ℚ)) he39
  rw [p3_even_moment_three]
  convert Interval.contains_add (Interval.contains_add (Interval.contains_add h0 h13) h26) h39
      using 1 <;> norm_num [p3TightMomentThree, p3TightRat]

private theorem p3TightMomentFour_contains :
    p3TightMomentFour.Contains (p3EvenMoment 4) := by
  have he13 := p3TightExpNegInterval_contains (x := (13 / 6 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he26 := p3TightExpNegInterval_contains (x := (26 / 3 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he39 := p3TightExpNegInterval_contains (x := (39 / 2 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he104 := p3TightExpNegInterval_contains (x := (104 / 3 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  norm_num at he13 he26 he39 he104
  have h0 := Interval.contains_ofRat p3TightCertificatePrecision (35 / 128 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (56 / 128 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (28 / 128 : ℚ)) he26
  have h39 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (8 / 128 : ℚ)) he39
  have h104 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (1 / 128 : ℚ)) he104
  rw [p3_even_moment_four]
  convert Interval.contains_add (Interval.contains_add (Interval.contains_add
      (Interval.contains_add h0 h13) h26) h39) h104 using 1 <;>
    norm_num [p3TightMomentFour, p3TightRat]

private theorem p3TightMomentFive_contains :
    p3TightMomentFive.Contains (p3EvenMoment 5) := by
  have he13 := p3TightExpNegInterval_contains (x := (13 / 6 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he26 := p3TightExpNegInterval_contains (x := (26 / 3 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he39 := p3TightExpNegInterval_contains (x := (39 / 2 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he104 := p3TightExpNegInterval_contains (x := (104 / 3 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he325 := p3TightExpNegInterval_contains (x := (325 / 6 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  norm_num at he13 he26 he39 he104 he325
  have h0 := Interval.contains_ofRat p3TightCertificatePrecision (126 / 512 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (210 / 512 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (120 / 512 : ℚ)) he26
  have h39 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (45 / 512 : ℚ)) he39
  have h104 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (10 / 512 : ℚ)) he104
  have h325 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (1 / 512 : ℚ)) he325
  rw [p3_even_moment_five]
  convert Interval.contains_add (Interval.contains_add (Interval.contains_add
      (Interval.contains_add (Interval.contains_add h0 h13) h26) h39) h104) h325 using 1 <;>
    norm_num [p3TightMomentFive, p3TightRat]

private theorem p3TightMomentSix_contains :
    p3TightMomentSix.Contains (p3EvenMoment 6) := by
  have he13 := p3TightExpNegInterval_contains (x := (13 / 6 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he26 := p3TightExpNegInterval_contains (x := (26 / 3 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he39 := p3TightExpNegInterval_contains (x := (39 / 2 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he104 := p3TightExpNegInterval_contains (x := (104 / 3 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he325 := p3TightExpNegInterval_contains (x := (325 / 6 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  have he78 := p3TightExpNegInterval_contains (x := (78 : ℚ))
    (by norm_num) (by norm_num [p3TightCertificateSquarings])
    (by decide +kernel)
    (by decide +kernel)
  norm_num at he13 he26 he39 he104 he325 he78
  have h0 := Interval.contains_ofRat p3TightCertificatePrecision (462 / 2048 : ℚ)
  have h13 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (792 / 2048 : ℚ)) he13
  have h26 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (495 / 2048 : ℚ)) he26
  have h39 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (220 / 2048 : ℚ)) he39
  have h104 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (66 / 2048 : ℚ)) he104
  have h325 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (12 / 2048 : ℚ)) he325
  have h78 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (1 / 2048 : ℚ)) he78
  rw [p3_even_moment_six]
  convert Interval.contains_add (Interval.contains_add (Interval.contains_add
      (Interval.contains_add (Interval.contains_add (Interval.contains_add
        h0 h13) h26) h39) h104) h325) h78 using 1 <;>
    norm_num [p3TightMomentSix, p3TightRat]

/-- The tight interval encloses the exact alternate six-moment endpoint. -/
theorem p3TightUpperInterval_contains :
    p3TightUpperInterval.Contains p3AlternateEndpoint := by
  have h1 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (14283 / 85750 : ℚ))
    p3TightMomentOne_contains
  have h2 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (153323 / 85750 : ℚ))
    p3TightMomentTwo_contains
  have h3 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (2769016 / 1157625 : ℚ))
    p3TightMomentThree_contains
  have h4 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (1040968 / 385875 : ℚ))
    p3TightMomentFour_contains
  have h5 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (93952 / 55125 : ℚ))
    p3TightMomentFive_contains
  have h6 := Interval.contains_mul
    (Interval.contains_ofRat p3TightCertificatePrecision (514048 / 1157625 : ℚ))
    p3TightMomentSix_contains
  have h12 := Interval.contains_add h1 h2
  have h123 := Interval.contains_sub h12 h3
  have h1234 := Interval.contains_add h123 h4
  have h12345 := Interval.contains_sub h1234 h5
  have h := Interval.contains_add h12345 h6
  simpa [p3TightUpperInterval, p3TightRat, p3AlternateEndpoint] using h

/-- Executable strict check for the tighter interpolation endpoint. -/
def p3TightCheck : Bool :=
  Interval.upperLTCheck p3TightUpperInterval (4831 / 10000)

/-- The tighter interpolation endpoint check closes by kernel reduction. -/
theorem p3TightCheck_eq_true : p3TightCheck = true := by
  decide +kernel

/-- The tight certificate proves the p=3 endpoint below `4831/10000`. -/
theorem p3TightEndpoint_lt_4831_over_10000 :
    p3AlternateEndpoint < (4831 / 10000 : ℝ) := by
  have h := Interval.lt_of_contains_of_upperLTCheck
    p3TightUpperInterval_contains p3TightCheck_eq_true
  convert h using 1
  norm_num

/-- The scalar p=3 profile satisfies the tight interpolation endpoint. -/
theorem sparseScalarF_13_div_4_three_lt_4831_over_10000 :
    sparseScalarF (13 / 4) 3 < (4831 / 10000 : ℝ) := by
  exact sparseScalarF_13_div_4_three_le_even_majorant.trans_lt
    p3TightEndpoint_lt_4831_over_10000

end DenseScalar
end CertifiedProjections
