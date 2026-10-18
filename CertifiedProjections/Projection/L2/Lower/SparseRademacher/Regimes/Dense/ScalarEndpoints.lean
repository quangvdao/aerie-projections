/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Analysis.Gaussian.GaussianCharacteristic
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.Moment
import Mathlib.Tactic.Ring

/-!
# Dense scalar endpoint producers

This module starts the dense `[3,8]` scalar slice.  The even endpoints are
proved from finite cosine-power identities and the Gaussian characteristic
function; no external numerical premise is used.
The interval-cell replay boundary will consume these endpoint producers in a
later module.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace CertifiedProjections
namespace DenseScalar

private lemma gaussian_const_integrable (c : ℝ) :
    Integrable (fun _ : ℝ => c) (gaussianReal 0 1) := by
  fun_prop

/-- The exact second-power Fourier identity used by the dense moments. -/
theorem cos_two_identity (x : ℝ) :
    |Real.cos x| ^ (2 : ℕ) = (1 : ℝ) / 2 + (1 / 2 : ℝ) * Real.cos (2 * x) := by
  rw [sq_abs, Real.cos_two_mul]
  ring

/-- The exact fourth-power Fourier identity used by the dense endpoint. -/
theorem cos_four_identity (x : ℝ) :
    |Real.cos x| ^ (4 : ℕ) =
      (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos (2 * x) +
        (1 / 8 : ℝ) * Real.cos (4 * x) := by
  have hcos : Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
    rw [Real.cos_two_mul]
    ring
  have habs : |Real.cos x| ^ (4 : ℕ) = Real.cos x ^ 4 := by
    calc
      |Real.cos x| ^ (4 : ℕ) = (|Real.cos x| ^ 2) ^ 2 := by ring
      _ = (Real.cos x ^ 2) ^ 2 := by rw [sq_abs]
      _ = Real.cos x ^ 4 := by ring
  have hcos4 : Real.cos (4 * x) =
      2 * Real.cos (2 * x) ^ 2 - 1 := by
    convert Real.cos_two_mul (2 * x) using 1
    ring_nf
  rw [habs, show Real.cos x ^ 4 = (Real.cos x ^ 2) ^ 2 by ring,
    hcos, hcos4]
  ring

/-- The exact sixth-power Fourier identity used by the dense endpoint. -/
theorem cos_six_identity (x : ℝ) :
    |Real.cos x| ^ (6 : ℕ) =
      (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos (2 * x) +
        (6 / 32 : ℝ) * Real.cos (4 * x) +
          (1 / 32 : ℝ) * Real.cos (6 * x) := by
  have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 :=
    Real.cos_two_mul x
  have h4 : Real.cos (4 * x) =
      2 * Real.cos (2 * x) ^ 2 - 1 := by
    convert Real.cos_two_mul (2 * x) using 1
    ring_nf
  have h6 : Real.cos (6 * x) =
      2 * (4 * Real.cos x ^ 3 - 3 * Real.cos x) ^ 2 - 1 := by
    rw [show 6 * x = 2 * (3 * x) by ring, Real.cos_two_mul,
      Real.cos_three_mul]
  have habs : |Real.cos x| ^ (6 : ℕ) = Real.cos x ^ 6 := by
    calc
      |Real.cos x| ^ (6 : ℕ) = (|Real.cos x| ^ 2) ^ 3 := by ring
      _ = (Real.cos x ^ 2) ^ 3 := by rw [sq_abs]
      _ = Real.cos x ^ 6 := by ring
  simp only [habs, h2, h4, h6]
  ring

/-- The exact eighth-power Fourier identity used by the dense endpoint. -/
theorem cos_eight_identity (x : ℝ) :
    |Real.cos x| ^ (8 : ℕ) =
      (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos (2 * x) +
        (28 / 128 : ℝ) * Real.cos (4 * x) +
          (8 / 128 : ℝ) * Real.cos (6 * x) +
            (1 / 128 : ℝ) * Real.cos (8 * x) := by
  have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 :=
    Real.cos_two_mul x
  have h4 : Real.cos (4 * x) =
      2 * Real.cos (2 * x) ^ 2 - 1 := by
    convert Real.cos_two_mul (2 * x) using 1
    ring_nf
  have h8 : Real.cos (8 * x) =
      2 * (2 * Real.cos (2 * x) ^ 2 - 1) ^ 2 - 1 := by
    rw [show 8 * x = 2 * (4 * x) by ring, Real.cos_two_mul, h4]
  have h6 : Real.cos (6 * x) =
      2 * (4 * Real.cos x ^ 3 - 3 * Real.cos x) ^ 2 - 1 := by
    rw [show 6 * x = 2 * (3 * x) by ring, Real.cos_two_mul,
      Real.cos_three_mul]
  have habs : |Real.cos x| ^ (8 : ℕ) = Real.cos x ^ 8 := by
    calc
      |Real.cos x| ^ (8 : ℕ) = (|Real.cos x| ^ 2) ^ 4 := by ring
      _ = (Real.cos x ^ 2) ^ 4 := by rw [sq_abs]
      _ = Real.cos x ^ 8 := by ring
  simp only [habs, h2, h4, h6, h8]
  ring

/-- The exact tenth-power Fourier identity used by the dense p=3 majorant. -/
theorem cos_ten_identity (x : ℝ) :
    |Real.cos x| ^ (10 : ℕ) =
      (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.cos (2 * x) +
        (120 / 512 : ℝ) * Real.cos (4 * x) +
          (45 / 512 : ℝ) * Real.cos (6 * x) +
            (10 / 512 : ℝ) * Real.cos (8 * x) +
              (1 / 512 : ℝ) * Real.cos (10 * x) := by
  have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 :=
    Real.cos_two_mul x
  have h4 : Real.cos (4 * x) =
      2 * Real.cos (2 * x) ^ 2 - 1 := by
    convert Real.cos_two_mul (2 * x) using 1
    ring_nf
  have h6 : Real.cos (6 * x) =
      2 * (4 * Real.cos x ^ 3 - 3 * Real.cos x) ^ 2 - 1 := by
    rw [show 6 * x = 2 * (3 * x) by ring, Real.cos_two_mul,
      Real.cos_three_mul]
  have hs : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq x
  have h5 : Real.cos (5 * x) =
      16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x := by
    rw [show 5 * x = 2 * x + 3 * x by ring, Real.cos_add,
      Real.cos_two_mul, Real.cos_three_mul, Real.sin_two_mul,
      Real.sin_three_mul]
    calc
      (2 * Real.cos x ^ 2 - 1) * (4 * Real.cos x ^ 3 - 3 * Real.cos x) -
          (2 * Real.sin x * Real.cos x) * (3 * Real.sin x - 4 * Real.sin x ^ 3) =
        16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x +
          (2 * Real.cos x - 8 * Real.cos x ^ 3 +
            8 * Real.cos x * Real.sin x ^ 2) *
            (Real.sin x ^ 2 + Real.cos x ^ 2 - 1) := by ring
      _ = 16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x := by
        rw [hs]
        ring
  have h8 : Real.cos (8 * x) =
      2 * (2 * Real.cos (2 * x) ^ 2 - 1) ^ 2 - 1 := by
    rw [show 8 * x = 2 * (4 * x) by ring, Real.cos_two_mul, h4]
  have h10 : Real.cos (10 * x) =
      2 * (16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 +
        5 * Real.cos x) ^ 2 - 1 := by
    rw [show 10 * x = 2 * (5 * x) by ring, Real.cos_two_mul, h5]
  have habs : |Real.cos x| ^ (10 : ℕ) = Real.cos x ^ 10 := by
    calc
      |Real.cos x| ^ (10 : ℕ) = (|Real.cos x| ^ 2) ^ 5 := by ring
      _ = (Real.cos x ^ 2) ^ 5 := by rw [sq_abs]
      _ = Real.cos x ^ 10 := by ring
  simp only [habs, h2, h4, h6, h8, h10]
  ring

/-- The exact twelfth-power Fourier identity used by the dense p=3 majorant. -/
theorem cos_twelve_identity (x : ℝ) :
    |Real.cos x| ^ (12 : ℕ) =
      (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.cos (2 * x) +
        (495 / 2048 : ℝ) * Real.cos (4 * x) +
          (220 / 2048 : ℝ) * Real.cos (6 * x) +
            (66 / 2048 : ℝ) * Real.cos (8 * x) +
              (12 / 2048 : ℝ) * Real.cos (10 * x) +
                (1 / 2048 : ℝ) * Real.cos (12 * x) := by
  have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 :=
    Real.cos_two_mul x
  have h4 : Real.cos (4 * x) =
      2 * Real.cos (2 * x) ^ 2 - 1 := by
    convert Real.cos_two_mul (2 * x) using 1
    ring_nf
  have h6 : Real.cos (6 * x) =
      2 * (4 * Real.cos x ^ 3 - 3 * Real.cos x) ^ 2 - 1 := by
    rw [show 6 * x = 2 * (3 * x) by ring, Real.cos_two_mul,
      Real.cos_three_mul]
  have h8 : Real.cos (8 * x) =
      2 * (2 * Real.cos (2 * x) ^ 2 - 1) ^ 2 - 1 := by
    rw [show 8 * x = 2 * (4 * x) by ring, Real.cos_two_mul, h4]
  have hs : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq x
  have h5 : Real.cos (5 * x) =
      16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x := by
    rw [show 5 * x = 2 * x + 3 * x by ring, Real.cos_add,
      Real.cos_two_mul, Real.cos_three_mul, Real.sin_two_mul,
      Real.sin_three_mul]
    calc
      (2 * Real.cos x ^ 2 - 1) * (4 * Real.cos x ^ 3 - 3 * Real.cos x) -
          (2 * Real.sin x * Real.cos x) * (3 * Real.sin x - 4 * Real.sin x ^ 3) =
        16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x +
          (2 * Real.cos x - 8 * Real.cos x ^ 3 +
            8 * Real.cos x * Real.sin x ^ 2) *
            (Real.sin x ^ 2 + Real.cos x ^ 2 - 1) := by ring
      _ = 16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x := by
        rw [hs]
        ring
  have h10 : Real.cos (10 * x) =
      2 * (16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 +
        5 * Real.cos x) ^ 2 - 1 := by
    rw [show 10 * x = 2 * (5 * x) by ring, Real.cos_two_mul, h5]
  have h12 : Real.cos (12 * x) =
      2 * (2 * (4 * Real.cos x ^ 3 - 3 * Real.cos x) ^ 2 - 1) ^ 2 - 1 := by
    rw [show 12 * x = 2 * (6 * x) by ring, Real.cos_two_mul, h6]
  have habs : |Real.cos x| ^ (12 : ℕ) = Real.cos x ^ 12 := by
    calc
      |Real.cos x| ^ (12 : ℕ) = (|Real.cos x| ^ 2) ^ 6 := by ring
      _ = (Real.cos x ^ 2) ^ 6 := by rw [sq_abs]
      _ = Real.cos x ^ 12 := by ring
  simp only [habs, h2, h4, h6, h8, h10, h12]
  ring

/-- The even endpoint exponents used by the compact dense profile. -/
def evenEndpointExponents : Finset ℕ := {4, 6, 8}

theorem evenEndpointExponents_mem_iff (p : ℕ) :
    p ∈ evenEndpointExponents ↔ p = 4 ∨ p = 6 ∨ p = 8 := by
  simp [evenEndpointExponents]

theorem sparseScalarF_13_div_4_four_exact :
    sparseScalarF (13 / 4) 4 =
      (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.exp (-(13 : ℝ) / 8) +
        (1 / 8 : ℝ) * Real.exp (-(13 : ℝ) / 2) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 4)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 4 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have h0 := gaussian_const_integrable (3 / 8 : ℝ)
  have h2 := gaussian_cos_integrable (2 * t)
  have h4 := gaussian_cos_integrable (4 * t)
  have hpoint (G : ℝ) :
      sparseScalarFIntegrand (13 / 4) 4 G =
        (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
          (1 / 8 : ℝ) * Real.cos ((4 * t) * G) := by
    dsimp [sparseScalarFIntegrand]
    change Real.rpow
        |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 4) * G)|
        ((4 : ℕ) : ℝ) = _
    calc
      Real.rpow
          |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 4) * G)|
          ((4 : ℕ) : ℝ) =
          |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 4) * G)| ^ (4 : ℕ) :=
        Real.rpow_natCast _ 4
      _ = _ := by
        simpa [t, mul_assoc] using
          cos_four_identity (Real.sqrt ((13 / 4 : ℝ) / 4) * G)
  unfold sparseScalarF
  calc
    (∫ G : ℝ, sparseScalarFIntegrand (13 / 4) 4 G
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
            (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
            ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ = (3 : ℝ) / 8 +
          (1 / 2 : ℝ) *
            (∫ G : ℝ, Real.cos ((2 * t) * G) ∂(gaussianReal 0 1)) +
          (1 / 8 : ℝ) *
            (∫ G : ℝ, Real.cos ((4 * t) * G) ∂(gaussianReal 0 1)) := by
      have h2i := gaussian_cos_integrable (2 * t)
      have h4i := gaussian_cos_integrable (4 * t)
      calc
        (∫ G : ℝ,
            (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
              (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1)) =
            (∫ G : ℝ,
              (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            (h0.add (h2i.const_mul (1 / 2 : ℝ)))
            (h4i.const_mul (1 / 8 : ℝ))
          simpa only [Pi.add_apply] using h
        _ = ((∫ G : ℝ, (3 : ℝ) / 8 ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 2 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            h0 (h2i.const_mul (1 / 2 : ℝ))
          simpa only [Pi.add_apply] using congrArg
            (fun z => z + ∫ G : ℝ, (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1)) h
        _ = (3 : ℝ) / 8 +
              (1 / 2 : ℝ) *
                (∫ G : ℝ, Real.cos ((2 * t) * G)
                  ∂(gaussianReal 0 1)) +
              (1 / 8 : ℝ) *
                (∫ G : ℝ, Real.cos ((4 * t) * G)
                  ∂(gaussianReal 0 1)) := by
          rw [integral_const_mul, integral_const_mul, integral_const]
          simp
    _ = (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (1 / 8 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) := by
      rw [gaussian_cosine_charFun, gaussian_cosine_charFun]
    _ = (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.exp (-(13 : ℝ) / 8) +
          (1 / 8 : ℝ) * Real.exp (-(13 : ℝ) / 2) := by
      have h2exp : -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 8 := by
        nlinarith [ht]
      have h4exp : -(4 * t) ^ 2 / 2 = -(13 : ℝ) / 2 := by
        nlinarith [ht]
      rw [h2exp, h4exp]

theorem sparseScalarF_13_div_4_six_exact :
    sparseScalarF (13 / 4) 6 =
      (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(13 : ℝ) / 12) +
        (6 / 32 : ℝ) * Real.exp (-(13 : ℝ) / 3) +
          (1 / 32 : ℝ) * Real.exp (-(39 : ℝ) / 4) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 6)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 6 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have h0 := gaussian_const_integrable (10 / 32 : ℝ)
  have h2 := gaussian_cos_integrable (2 * t)
  have h4 := gaussian_cos_integrable (4 * t)
  have h6 := gaussian_cos_integrable (6 * t)
  have hpoint (G : ℝ) :
      sparseScalarFIntegrand (13 / 4) 6 G =
        (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
          (6 / 32 : ℝ) * Real.cos ((4 * t) * G) +
            (1 / 32 : ℝ) * Real.cos ((6 * t) * G) := by
    dsimp [sparseScalarFIntegrand]
    change Real.rpow
        |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 6) * G)|
        ((6 : ℕ) : ℝ) = _
    calc
      Real.rpow
          |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 6) * G)|
          ((6 : ℕ) : ℝ) =
          |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 6) * G)| ^ (6 : ℕ) :=
        Real.rpow_natCast _ 6
      _ = _ := by
        simpa [t, mul_assoc] using
          cos_six_identity (Real.sqrt ((13 / 4 : ℝ) / 6) * G)
  unfold sparseScalarF
  calc
    (∫ G : ℝ, sparseScalarFIntegrand (13 / 4) 6 G
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
            (6 / 32 : ℝ) * Real.cos ((4 * t) * G) +
              (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
            ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ = (10 : ℝ) / 32 +
          (15 / 32 : ℝ) *
            (∫ G : ℝ, Real.cos ((2 * t) * G) ∂(gaussianReal 0 1)) +
          (6 / 32 : ℝ) *
            (∫ G : ℝ, Real.cos ((4 * t) * G) ∂(gaussianReal 0 1)) +
          (1 / 32 : ℝ) *
            (∫ G : ℝ, Real.cos ((6 * t) * G) ∂(gaussianReal 0 1)) := by
      have h2i := gaussian_cos_integrable (2 * t)
      have h4i := gaussian_cos_integrable (4 * t)
      have h6i := gaussian_cos_integrable (6 * t)
      calc
        (∫ G : ℝ,
            (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
              (6 / 32 : ℝ) * Real.cos ((4 * t) * G) +
                (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
              ∂(gaussianReal 0 1)) =
            (∫ G : ℝ,
              (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
                (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            ((h0.add (h2i.const_mul (15 / 32 : ℝ))).add
              (h4i.const_mul (6 / 32 : ℝ)))
            (h6i.const_mul (1 / 32 : ℝ))
          simpa only [Pi.add_apply] using h
        _ = ((∫ G : ℝ,
              (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            (h0.add (h2i.const_mul (15 / 32 : ℝ)))
            (h4i.const_mul (6 / 32 : ℝ))
          simpa only [Pi.add_apply] using congrArg
            (fun z => z + ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
              ∂(gaussianReal 0 1)) h
        _ = (((∫ G : ℝ, (10 : ℝ) / 32 ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (15 / 32 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            h0 (h2i.const_mul (15 / 32 : ℝ))
          simpa only [Pi.add_apply] using congrArg
            (fun z => z + ∫ G : ℝ, (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1) +
                ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
                  ∂(gaussianReal 0 1)) h
        _ = (10 : ℝ) / 32 +
              (15 / 32 : ℝ) *
                (∫ G : ℝ, Real.cos ((2 * t) * G)
                  ∂(gaussianReal 0 1)) +
              (6 / 32 : ℝ) *
                (∫ G : ℝ, Real.cos ((4 * t) * G)
                  ∂(gaussianReal 0 1)) +
              (1 / 32 : ℝ) *
                (∫ G : ℝ, Real.cos ((6 * t) * G)
                  ∂(gaussianReal 0 1)) := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul,
            integral_const]
          simp
    _ = (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (6 / 32 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (1 / 32 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) := by
      rw [gaussian_cosine_charFun, gaussian_cosine_charFun,
        gaussian_cosine_charFun]
    _ = (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(13 : ℝ) / 12) +
          (6 / 32 : ℝ) * Real.exp (-(13 : ℝ) / 3) +
            (1 / 32 : ℝ) * Real.exp (-(39 : ℝ) / 4) := by
      have h2exp : -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 12 := by
        nlinarith [ht]
      have h4exp : -(4 * t) ^ 2 / 2 = -(13 : ℝ) / 3 := by
        nlinarith [ht]
      have h6exp : -(6 * t) ^ 2 / 2 = -(39 : ℝ) / 4 := by
        nlinarith [ht]
      rw [h2exp, h4exp, h6exp]

theorem sparseScalarF_13_div_4_eight_exact :
    sparseScalarF (13 / 4) 8 =
      (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(13 : ℝ) / 16) +
        (28 / 128 : ℝ) * Real.exp (-(13 : ℝ) / 4) +
          (8 / 128 : ℝ) * Real.exp (-(117 : ℝ) / 16) +
            (1 / 128 : ℝ) * Real.exp (-(13 : ℝ) / 1) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 8)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 8 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have h0 := gaussian_const_integrable (35 / 128 : ℝ)
  have h2 := gaussian_cos_integrable (2 * t)
  have h4 := gaussian_cos_integrable (4 * t)
  have h6 := gaussian_cos_integrable (6 * t)
  have h8 := gaussian_cos_integrable (8 * t)
  have hpoint (G : ℝ) :
      sparseScalarFIntegrand (13 / 4) 8 G =
        (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
          (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
            (8 / 128 : ℝ) * Real.cos ((6 * t) * G) +
              (1 / 128 : ℝ) * Real.cos ((8 * t) * G) := by
    dsimp [sparseScalarFIntegrand]
    change Real.rpow
        |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 8) * G)|
        ((8 : ℕ) : ℝ) = _
    calc
      Real.rpow
          |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 8) * G)|
          ((8 : ℕ) : ℝ) =
          |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 8) * G)| ^ (8 : ℕ) :=
        Real.rpow_natCast _ 8
      _ = _ := by
        simpa [t, mul_assoc] using
          cos_eight_identity (Real.sqrt ((13 / 4 : ℝ) / 8) * G)
  unfold sparseScalarF
  calc
    (∫ G : ℝ, sparseScalarFIntegrand (13 / 4) 8 G
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
            (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
              (8 / 128 : ℝ) * Real.cos ((6 * t) * G) +
                (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
            ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ = (35 : ℝ) / 128 +
          (56 / 128 : ℝ) *
            (∫ G : ℝ, Real.cos ((2 * t) * G) ∂(gaussianReal 0 1)) +
          (28 / 128 : ℝ) *
            (∫ G : ℝ, Real.cos ((4 * t) * G) ∂(gaussianReal 0 1)) +
          (8 / 128 : ℝ) *
            (∫ G : ℝ, Real.cos ((6 * t) * G) ∂(gaussianReal 0 1)) +
          (1 / 128 : ℝ) *
            (∫ G : ℝ, Real.cos ((8 * t) * G) ∂(gaussianReal 0 1)) := by
      have h2i := gaussian_cos_integrable (2 * t)
      have h4i := gaussian_cos_integrable (4 * t)
      have h6i := gaussian_cos_integrable (6 * t)
      have h8i := gaussian_cos_integrable (8 * t)
      calc
        (∫ G : ℝ,
            (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
              (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
                (8 / 128 : ℝ) * Real.cos ((6 * t) * G) +
                  (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
              ∂(gaussianReal 0 1)) =
            (∫ G : ℝ,
              (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
                (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
                  (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            (((h0.add (h2i.const_mul (56 / 128 : ℝ))).add
              (h4i.const_mul (28 / 128 : ℝ))).add
                (h6i.const_mul (8 / 128 : ℝ)))
            (h8i.const_mul (1 / 128 : ℝ))
          simpa only [Pi.add_apply] using h
        _ = ((∫ G : ℝ,
              (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
                (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            ((h0.add (h2i.const_mul (56 / 128 : ℝ))).add
              (h4i.const_mul (28 / 128 : ℝ)))
            (h6i.const_mul (8 / 128 : ℝ))
          simpa only [Pi.add_apply] using congrArg
            (fun z => z + ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
              ∂(gaussianReal 0 1)) h
        _ = (((∫ G : ℝ,
              (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            (h0.add (h2i.const_mul (56 / 128 : ℝ)))
            (h4i.const_mul (28 / 128 : ℝ))
          simpa only [Pi.add_apply] using congrArg
            (fun z => z + ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
              ∂(gaussianReal 0 1) +
                ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                  ∂(gaussianReal 0 1)) h
        _ = ((((∫ G : ℝ, (35 : ℝ) / 128 ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (56 / 128 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h := integral_add (μ := gaussianReal 0 1)
            h0 (h2i.const_mul (56 / 128 : ℝ))
          simpa only [Pi.add_apply] using congrArg
            (fun z => z + ∫ G : ℝ, (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1) +
                ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                  ∂(gaussianReal 0 1) +
                ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                  ∂(gaussianReal 0 1)) h
        _ = (35 : ℝ) / 128 +
              (56 / 128 : ℝ) *
                (∫ G : ℝ, Real.cos ((2 * t) * G)
                  ∂(gaussianReal 0 1)) +
              (28 / 128 : ℝ) *
                (∫ G : ℝ, Real.cos ((4 * t) * G)
                  ∂(gaussianReal 0 1)) +
              (8 / 128 : ℝ) *
                (∫ G : ℝ, Real.cos ((6 * t) * G)
                  ∂(gaussianReal 0 1)) +
              (1 / 128 : ℝ) *
                (∫ G : ℝ, Real.cos ((8 * t) * G)
                  ∂(gaussianReal 0 1)) := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul,
            integral_const_mul, integral_const]
          simp
    _ = (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (28 / 128 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (8 / 128 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
              (1 / 128 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) := by
      rw [gaussian_cosine_charFun, gaussian_cosine_charFun,
        gaussian_cosine_charFun, gaussian_cosine_charFun]
    _ = (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(13 : ℝ) / 16) +
          (28 / 128 : ℝ) * Real.exp (-(13 : ℝ) / 4) +
            (8 / 128 : ℝ) * Real.exp (-(117 : ℝ) / 16) +
              (1 / 128 : ℝ) * Real.exp (-(13 : ℝ) / 1) := by
      have h2exp : -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 16 := by
        nlinarith [ht]
      have h4exp : -(4 * t) ^ 2 / 2 = -(13 : ℝ) / 4 := by
        nlinarith [ht]
      have h6exp : -(6 * t) ^ 2 / 2 = -(117 : ℝ) / 16 := by
        nlinarith [ht]
      have h8exp : -(8 * t) ^ 2 / 2 = -(13 : ℝ) / 1 := by
        nlinarith [ht]
      rw [h2exp, h4exp, h6exp, h8exp]

end DenseScalar
end CertifiedProjections
