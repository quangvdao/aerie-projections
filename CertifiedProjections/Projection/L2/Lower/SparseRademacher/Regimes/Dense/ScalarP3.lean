/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Regimes.Dense.ScalarEndpoints
import Mathlib.Tactic.Ring

/-!
# Dense scalar `p = 3` producer

This module supplies a proved, finite polynomial majorant for the odd dense
profile.  It is deliberately a semantic producer: the later dense certificate
may replace its numerical evaluation boundary without importing row, PMF, or
certificate data.

The majorant is written in `u = cos² x`.  Its difference from `|cos x|³`
factors into nonnegative squares, so no sampled numerical premise is hidden in
the analytic theorem.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

noncomputable section

namespace CertifiedProjections
namespace DenseScalar

private lemma gaussian_cos_power_integrable (t : ℝ) (n : ℕ) :
    Integrable (fun G : ℝ => Real.cos (t * G) ^ n)
      (gaussianReal 0 1) := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [] with G
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)

private lemma gaussian_integral_fourier4 (t : ℝ) :
    (∫ G : ℝ,
      (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
        (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
      ∂(gaussianReal 0 1)) =
      (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
        (1 / 8 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) := by
  have h0 : Integrable (fun _ : ℝ => (3 : ℝ) / 8)
      (gaussianReal 0 1) := by fun_prop
  have h2 := gaussian_cos_integrable (2 * t)
  have h4 := gaussian_cos_integrable (4 * t)
  have h := integral_add (μ := gaussianReal 0 1)
    (h0.add (h2.const_mul (1 / 2 : ℝ)))
    (h4.const_mul (1 / 8 : ℝ))
  calc
    (∫ G : ℝ,
        (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
          (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
        ∂(gaussianReal 0 1)) =
        ((∫ G : ℝ, (3 : ℝ) / 8 +
            (1 / 2 : ℝ) * Real.cos ((2 * t) * G)
            ∂(gaussianReal 0 1)) +
          ∫ G : ℝ, (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
            ∂(gaussianReal 0 1)) := by
      simpa only [Pi.add_apply] using h
    _ = (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (1 / 8 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) := by
      rw [integral_add h0 (h2.const_mul (1 / 2 : ℝ)), integral_const,
        integral_const_mul, integral_const_mul, gaussian_cosine_charFun,
        gaussian_cosine_charFun]
      simp

private lemma gaussian_integral_fourier6 (t : ℝ) :
    (∫ G : ℝ,
      (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
        (6 / 32 : ℝ) * Real.cos ((4 * t) * G) +
          (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
      ∂(gaussianReal 0 1)) =
      (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
        (6 / 32 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
          (1 / 32 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) := by
  have h0 : Integrable (fun _ : ℝ => (10 : ℝ) / 32)
      (gaussianReal 0 1) := by fun_prop
  have h2 := gaussian_cos_integrable (2 * t)
  have h4 := gaussian_cos_integrable (4 * t)
  have h6 := gaussian_cos_integrable (6 * t)
  have h₁ := h0.add (h2.const_mul (15 / 32 : ℝ))
  have h₂ := h4.const_mul (6 / 32 : ℝ)
  have h₃ := h6.const_mul (1 / 32 : ℝ)
  have h := integral_add (μ := gaussianReal 0 1) (h₁.add h₂) h₃
  calc
    (∫ G : ℝ,
        (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
          (6 / 32 : ℝ) * Real.cos ((4 * t) * G) +
            (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          ((10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
            (6 / 32 : ℝ) * Real.cos ((4 * t) * G)) +
              (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
          ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      ring
    _ = (∫ G : ℝ,
          (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
            (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
          ∂(gaussianReal 0 1)) +
          ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
            ∂(gaussianReal 0 1) := by
      simpa only [Pi.add_apply] using h
    _ = (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (6 / 32 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (1 / 32 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) := by
      have hfirst := integral_add (μ := gaussianReal 0 1) h₁ h₂
      have hsecond := integral_add (μ := gaussianReal 0 1) h0
        (h2.const_mul (15 / 32 : ℝ))
      calc
        (∫ G : ℝ,
            (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
              (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
            ∂(gaussianReal 0 1)) +
            ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
              ∂(gaussianReal 0 1) =
            ((∫ G : ℝ, (10 : ℝ) / 32 +
                (15 / 32 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h' := congrArg
            (fun z => z + ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
              ∂(gaussianReal 0 1)) hfirst
          simpa only [Pi.add_apply] using h'
        _ = (((∫ G : ℝ, (10 : ℝ) / 32 ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (15 / 32 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h' := congrArg
            (fun z => z + ∫ G : ℝ, (6 / 32 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1) +
              ∫ G : ℝ, (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) hsecond
          simpa only [Pi.add_apply] using h'
        _ = (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
              (6 / 32 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
                (1 / 32 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) := by
          rw [integral_const, integral_const_mul, integral_const_mul,
            integral_const_mul, gaussian_cosine_charFun,
            gaussian_cosine_charFun, gaussian_cosine_charFun]
          simp

private lemma gaussian_integral_fourier8 (t : ℝ) :
    (∫ G : ℝ,
      (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
        (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
          (8 / 128 : ℝ) * Real.cos ((6 * t) * G) +
            (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
      ∂(gaussianReal 0 1)) =
      (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
        (28 / 128 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
          (8 / 128 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
            (1 / 128 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) := by
  have h0 : Integrable (fun _ : ℝ => (35 : ℝ) / 128)
      (gaussianReal 0 1) := by fun_prop
  have h2 := gaussian_cos_integrable (2 * t)
  have h4 := gaussian_cos_integrable (4 * t)
  have h6 := gaussian_cos_integrable (6 * t)
  have h8 := gaussian_cos_integrable (8 * t)
  have h₁ := h0.add (h2.const_mul (56 / 128 : ℝ))
  have h₂ := h4.const_mul (28 / 128 : ℝ)
  have h₃ := h6.const_mul (8 / 128 : ℝ)
  have h₄ := h8.const_mul (1 / 128 : ℝ)
  have h := integral_add (μ := gaussianReal 0 1) ((h₁.add h₂).add h₃) h₄
  calc
    (∫ G : ℝ,
        (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
          (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
            (8 / 128 : ℝ) * Real.cos ((6 * t) * G) +
              (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          (((35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
            (28 / 128 : ℝ) * Real.cos ((4 * t) * G)) +
              (8 / 128 : ℝ) * Real.cos ((6 * t) * G)) +
                (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
          ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      ring
    _ = (∫ G : ℝ,
          ((35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
            (28 / 128 : ℝ) * Real.cos ((4 * t) * G)) +
              (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
          ∂(gaussianReal 0 1)) +
          ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
            ∂(gaussianReal 0 1) := by
      simpa only [Pi.add_apply] using h
    _ = (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (28 / 128 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (8 / 128 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
              (1 / 128 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) := by
      have hfirst := integral_add (μ := gaussianReal 0 1)
        (h₁.add h₂) h₃
      have hsecond := integral_add (μ := gaussianReal 0 1) h₁ h₂
      have hthird := integral_add (μ := gaussianReal 0 1) h0
        (h2.const_mul (56 / 128 : ℝ))
      calc
        (∫ G : ℝ,
            (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
              (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
                (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
            ∂(gaussianReal 0 1)) +
            ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
              ∂(gaussianReal 0 1) =
            ((∫ G : ℝ,
                (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
                  (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h' := congrArg
            (fun z => z + ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
              ∂(gaussianReal 0 1)) hfirst
          simpa only [Pi.add_apply] using h'
        _ = (((∫ G : ℝ, (35 : ℝ) / 128 +
                (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
                  (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1)) := by
          rfl
        _ = (((∫ G : ℝ, (35 : ℝ) / 128 +
                (56 / 128 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h' := congrArg
            (fun z => z + ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
              ∂(gaussianReal 0 1) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1)) hsecond
          simpa only [Pi.add_apply] using h'
        _ = ((((∫ G : ℝ, (35 : ℝ) / 128 ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (56 / 128 : ℝ) * Real.cos ((2 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1) := by
          have h' := congrArg
            (fun z => z + ∫ G : ℝ, (28 / 128 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1) +
              ∫ G : ℝ, (8 / 128 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1) +
              ∫ G : ℝ, (1 / 128 : ℝ) * Real.cos ((8 * t) * G)
                ∂(gaussianReal 0 1)) hthird
          simpa only [Pi.add_apply] using h'
        _ = (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
              (28 / 128 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
                (8 / 128 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
                  (1 / 128 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) := by
          rw [integral_const, integral_const_mul, integral_const_mul,
            integral_const_mul, integral_const_mul, gaussian_cosine_charFun,
            gaussian_cosine_charFun, gaussian_cosine_charFun,
            gaussian_cosine_charFun]
          simp

private lemma integral_six_linear {μ : Measure ℝ}
    {f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ)
    (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ)
    (h₅ : Integrable f₅ μ) (h₆ : Integrable f₆ μ) :
    (∫ x : ℝ, f₁ x + f₂ x - f₃ x + f₄ x - f₅ x + f₆ x ∂μ) =
      (∫ x : ℝ, f₁ x ∂μ) + (∫ x : ℝ, f₂ x ∂μ) -
        (∫ x : ℝ, f₃ x ∂μ) + (∫ x : ℝ, f₄ x ∂μ) -
          (∫ x : ℝ, f₅ x ∂μ) + (∫ x : ℝ, f₆ x ∂μ) := by
  have h₁₂ := integral_add (μ := μ) h₁ h₂
  have h₁₂₃ := integral_sub (μ := μ) (h₁.add h₂) h₃
  have h₁₂₃₄ := integral_add (μ := μ) ((h₁.add h₂).sub h₃) h₄
  have h₁₂₃₄₅ := integral_sub (μ := μ)
    (((h₁.add h₂).sub h₃).add h₄) h₅
  have h₁₂₃₄₅₆ := integral_add (μ := μ)
    ((((h₁.add h₂).sub h₃).add h₄).sub h₅) h₆
  calc
    (∫ x : ℝ, f₁ x + f₂ x - f₃ x + f₄ x - f₅ x + f₆ x ∂μ) =
        ∫ x : ℝ,
          (((((f₁ + f₂) - f₃) + f₄) - f₅) + f₆) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rfl
    _ = (∫ x : ℝ, ((((f₁ + f₂) - f₃) + f₄) - f₅) x ∂μ) +
        (∫ x : ℝ, f₆ x ∂μ) := by
      simpa only [Pi.add_apply, Pi.sub_apply] using h₁₂₃₄₅₆
    _ = ((∫ x : ℝ, (((f₁ + f₂) - f₃) + f₄) x ∂μ) -
          (∫ x : ℝ, f₅ x ∂μ)) + (∫ x : ℝ, f₆ x ∂μ) := by
      have h := congrArg
        (fun z => z + (∫ x : ℝ, f₆ x ∂μ)) h₁₂₃₄₅
      simpa only [Pi.add_apply, Pi.sub_apply] using h
    _ = (((∫ x : ℝ, ((f₁ + f₂) - f₃) x ∂μ) +
          (∫ x : ℝ, f₄ x ∂μ)) - (∫ x : ℝ, f₅ x ∂μ)) +
          (∫ x : ℝ, f₆ x ∂μ) := by
      have h := congrArg
        (fun z => z - (∫ x : ℝ, f₅ x ∂μ) +
          (∫ x : ℝ, f₆ x ∂μ)) h₁₂₃₄
      simpa only [Pi.add_apply, Pi.sub_apply] using h
    _ = ((((∫ x : ℝ, (f₁ + f₂) x ∂μ) -
          (∫ x : ℝ, f₃ x ∂μ)) + (∫ x : ℝ, f₄ x ∂μ)) -
          (∫ x : ℝ, f₅ x ∂μ)) + (∫ x : ℝ, f₆ x ∂μ) := by
      have h := congrArg
        (fun z => z + (∫ x : ℝ, f₄ x ∂μ) -
          (∫ x : ℝ, f₅ x ∂μ) + (∫ x : ℝ, f₆ x ∂μ)) h₁₂₃
      simpa only [Pi.add_apply, Pi.sub_apply] using h
    _ = (((((∫ x : ℝ, f₁ x ∂μ) +
          (∫ x : ℝ, f₂ x ∂μ)) - (∫ x : ℝ, f₃ x ∂μ)) +
          (∫ x : ℝ, f₄ x ∂μ)) - (∫ x : ℝ, f₅ x ∂μ)) +
          (∫ x : ℝ, f₆ x ∂μ) := by
      have h := congrArg
        (fun z => z - (∫ x : ℝ, f₃ x ∂μ) +
          (∫ x : ℝ, f₄ x ∂μ) - (∫ x : ℝ, f₅ x ∂μ) +
          (∫ x : ℝ, f₆ x ∂μ)) h₁₂
      simpa only [Pi.add_apply, Pi.sub_apply] using h

private lemma integral_six_add {μ : Measure ℝ}
    {f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ)
    (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ)
    (h₅ : Integrable f₅ μ) (h₆ : Integrable f₆ μ) :
    (∫ x : ℝ, f₁ x + f₂ x + f₃ x + f₄ x + f₅ x + f₆ x ∂μ) =
      (∫ x : ℝ, f₁ x ∂μ) + (∫ x : ℝ, f₂ x ∂μ) +
        (∫ x : ℝ, f₃ x ∂μ) + (∫ x : ℝ, f₄ x ∂μ) +
          (∫ x : ℝ, f₅ x ∂μ) + (∫ x : ℝ, f₆ x ∂μ) := by
  have h := integral_six_linear h₁ h₂ h₃.neg h₄ h₅.neg h₆
  calc
    (∫ x : ℝ, f₁ x + f₂ x + f₃ x + f₄ x + f₅ x + f₆ x ∂μ) =
        ∫ x : ℝ,
          f₁ x + f₂ x - (-f₃ x) + f₄ x - (-f₅ x) + f₆ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (∫ x : ℝ, f₁ x ∂μ) + (∫ x : ℝ, f₂ x ∂μ) -
          (∫ x : ℝ, (-f₃ x) ∂μ) + (∫ x : ℝ, f₄ x ∂μ) -
            (∫ x : ℝ, (-f₅ x) ∂μ) + (∫ x : ℝ, f₆ x ∂μ) := h
    _ = (∫ x : ℝ, f₁ x ∂μ) + (∫ x : ℝ, f₂ x ∂μ) +
          (∫ x : ℝ, f₃ x ∂μ) + (∫ x : ℝ, f₄ x ∂μ) +
            (∫ x : ℝ, f₅ x ∂μ) + (∫ x : ℝ, f₆ x ∂μ) := by
      rw [integral_neg, integral_neg]
      ring

private lemma gaussian_integral_fourier10 (t : ℝ) :
    (∫ G : ℝ,
      (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.cos ((2 * t) * G) +
        (120 / 512 : ℝ) * Real.cos ((4 * t) * G) +
          (45 / 512 : ℝ) * Real.cos ((6 * t) * G) +
            (10 / 512 : ℝ) * Real.cos ((8 * t) * G) +
              (1 / 512 : ℝ) * Real.cos ((10 * t) * G)
      ∂(gaussianReal 0 1)) =
      (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
        (120 / 512 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
          (45 / 512 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
            (10 / 512 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) +
              (1 / 512 : ℝ) * Real.exp (-(10 * t) ^ 2 / 2) := by
  have h0 : Integrable (fun _ : ℝ => (126 : ℝ) / 512)
      (gaussianReal 0 1) := by fun_prop
  have h2 := gaussian_cos_integrable (2 * t)
  have h4 := gaussian_cos_integrable (4 * t)
  have h6 := gaussian_cos_integrable (6 * t)
  have h8 := gaussian_cos_integrable (8 * t)
  have h10 := gaussian_cos_integrable (10 * t)
  have h := integral_six_add (μ := gaussianReal 0 1) h0
    (h2.const_mul (210 / 512 : ℝ))
    (h4.const_mul (120 / 512 : ℝ))
    (h6.const_mul (45 / 512 : ℝ))
    (h8.const_mul (10 / 512 : ℝ))
    (h10.const_mul (1 / 512 : ℝ))
  calc
    (∫ G : ℝ,
        (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.cos ((2 * t) * G) +
          (120 / 512 : ℝ) * Real.cos ((4 * t) * G) +
            (45 / 512 : ℝ) * Real.cos ((6 * t) * G) +
              (10 / 512 : ℝ) * Real.cos ((8 * t) * G) +
                (1 / 512 : ℝ) * Real.cos ((10 * t) * G)
        ∂(gaussianReal 0 1)) =
        (∫ G : ℝ, (126 : ℝ) / 512 ∂(gaussianReal 0 1)) +
          (∫ G : ℝ, (210 / 512 : ℝ) * Real.cos ((2 * t) * G)
            ∂(gaussianReal 0 1)) +
            (∫ G : ℝ, (120 / 512 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1)) +
              (∫ G : ℝ, (45 / 512 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
                (∫ G : ℝ, (10 / 512 : ℝ) * Real.cos ((8 * t) * G)
                  ∂(gaussianReal 0 1)) +
                  (∫ G : ℝ, (1 / 512 : ℝ) * Real.cos ((10 * t) * G)
                    ∂(gaussianReal 0 1)) := by
      simpa only [Pi.add_apply] using h
    _ = (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (120 / 512 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (45 / 512 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
              (10 / 512 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) +
                (1 / 512 : ℝ) * Real.exp (-(10 * t) ^ 2 / 2) := by
      rw [integral_const, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul,
        gaussian_cosine_charFun, gaussian_cosine_charFun,
        gaussian_cosine_charFun, gaussian_cosine_charFun,
        gaussian_cosine_charFun]
      simp

private lemma gaussian_integral_fourier12 (t : ℝ) :
    (∫ G : ℝ,
      (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.cos ((2 * t) * G) +
        (495 / 2048 : ℝ) * Real.cos ((4 * t) * G) +
          (220 / 2048 : ℝ) * Real.cos ((6 * t) * G) +
            (66 / 2048 : ℝ) * Real.cos ((8 * t) * G) +
              (12 / 2048 : ℝ) * Real.cos ((10 * t) * G) +
                (1 / 2048 : ℝ) * Real.cos ((12 * t) * G)
      ∂(gaussianReal 0 1)) =
      (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
        (495 / 2048 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
          (220 / 2048 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
            (66 / 2048 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) +
              (12 / 2048 : ℝ) * Real.exp (-(10 * t) ^ 2 / 2) +
                (1 / 2048 : ℝ) * Real.exp (-(12 * t) ^ 2 / 2) := by
  have h0 : Integrable (fun _ : ℝ => (462 : ℝ) / 2048)
      (gaussianReal 0 1) := by fun_prop
  have h2 := gaussian_cos_integrable (2 * t)
  have h4 := gaussian_cos_integrable (4 * t)
  have h6 := gaussian_cos_integrable (6 * t)
  have h8 := gaussian_cos_integrable (8 * t)
  have h10 := gaussian_cos_integrable (10 * t)
  have h12 := gaussian_cos_integrable (12 * t)
  have hfirst := integral_six_add (μ := gaussianReal 0 1) h0
    (h2.const_mul (792 / 2048 : ℝ))
    (h4.const_mul (495 / 2048 : ℝ))
    (h6.const_mul (220 / 2048 : ℝ))
    (h8.const_mul (66 / 2048 : ℝ))
    (h10.const_mul (12 / 2048 : ℝ))
  have hfirstInt : Integrable (fun G : ℝ =>
      (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.cos ((2 * t) * G) +
        (495 / 2048 : ℝ) * Real.cos ((4 * t) * G) +
          (220 / 2048 : ℝ) * Real.cos ((6 * t) * G) +
            (66 / 2048 : ℝ) * Real.cos ((8 * t) * G) +
              (12 / 2048 : ℝ) * Real.cos ((10 * t) * G))
      (gaussianReal 0 1) := by
    exact (((((h0.add (h2.const_mul (792 / 2048 : ℝ))).add
      (h4.const_mul (495 / 2048 : ℝ))).add
        (h6.const_mul (220 / 2048 : ℝ))).add
          (h8.const_mul (66 / 2048 : ℝ))).add
            (h10.const_mul (12 / 2048 : ℝ)))
  have h := integral_add (μ := gaussianReal 0 1) hfirstInt
    (h12.const_mul (1 / 2048 : ℝ))
  calc
    (∫ G : ℝ,
        (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.cos ((2 * t) * G) +
          (495 / 2048 : ℝ) * Real.cos ((4 * t) * G) +
            (220 / 2048 : ℝ) * Real.cos ((6 * t) * G) +
              (66 / 2048 : ℝ) * Real.cos ((8 * t) * G) +
                (12 / 2048 : ℝ) * Real.cos ((10 * t) * G) +
                  (1 / 2048 : ℝ) * Real.cos ((12 * t) * G)
        ∂(gaussianReal 0 1)) =
        (∫ G : ℝ,
          (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.cos ((2 * t) * G) +
            (495 / 2048 : ℝ) * Real.cos ((4 * t) * G) +
              (220 / 2048 : ℝ) * Real.cos ((6 * t) * G) +
                (66 / 2048 : ℝ) * Real.cos ((8 * t) * G) +
                  (12 / 2048 : ℝ) * Real.cos ((10 * t) * G)
          ∂(gaussianReal 0 1)) +
          (∫ G : ℝ, (1 / 2048 : ℝ) * Real.cos ((12 * t) * G)
            ∂(gaussianReal 0 1)) := by
      simpa only [Pi.add_apply] using h
    _ = ((∫ G : ℝ, (462 : ℝ) / 2048 ∂(gaussianReal 0 1)) +
          (∫ G : ℝ, (792 / 2048 : ℝ) * Real.cos ((2 * t) * G)
            ∂(gaussianReal 0 1)) +
            (∫ G : ℝ, (495 / 2048 : ℝ) * Real.cos ((4 * t) * G)
              ∂(gaussianReal 0 1)) +
              (∫ G : ℝ, (220 / 2048 : ℝ) * Real.cos ((6 * t) * G)
                ∂(gaussianReal 0 1)) +
                (∫ G : ℝ, (66 / 2048 : ℝ) * Real.cos ((8 * t) * G)
                  ∂(gaussianReal 0 1)) +
                  (∫ G : ℝ, (12 / 2048 : ℝ) * Real.cos ((10 * t) * G)
                    ∂(gaussianReal 0 1))) +
          (∫ G : ℝ, (1 / 2048 : ℝ) * Real.cos ((12 * t) * G)
            ∂(gaussianReal 0 1)) := by
      rw [hfirst]
    _ = (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (495 / 2048 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (220 / 2048 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
              (66 / 2048 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) +
                (12 / 2048 : ℝ) * Real.exp (-(10 * t) ^ 2 / 2) +
                  (1 / 2048 : ℝ) * Real.exp (-(12 * t) ^ 2 / 2) := by
      rw [integral_const, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, gaussian_cosine_charFun,
        gaussian_cosine_charFun, gaussian_cosine_charFun,
        gaussian_cosine_charFun, gaussian_cosine_charFun,
        gaussian_cosine_charFun]
      simp

private lemma abs_pow_even (x : ℝ) (n : ℕ) :
    |x| ^ (2 * n) = x ^ (2 * n) := by
  calc
    |x| ^ (2 * n) = (|x| ^ 2) ^ n := by rw [pow_mul]
    _ = (x ^ 2) ^ n := by rw [sq_abs]
    _ = x ^ (2 * n) := by rw [pow_mul]

private def p3Argument (G : ℝ) : ℝ :=
  Real.sqrt ((13 / 4 : ℝ) / 3) * G

/-- The nth even cosine moment at the dense p=3 scale `s = 13/4`. -/
def p3EvenMoment (n : ℕ) : ℝ :=
  ∫ G : ℝ, Real.cos (p3Argument G) ^ (2 * n) ∂(gaussianReal 0 1)

/-- Exact Gaussian evaluation of the second cosine moment. -/
theorem p3_even_moment_one :
    p3EvenMoment 1 = (1 : ℝ) / 2 + (1 / 2 : ℝ) * Real.exp (-(13 : ℝ) / 6) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 3)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 3 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have h0 : Integrable (fun _ : ℝ => (1 : ℝ) / 2)
      (gaussianReal 0 1) := by fun_prop
  have h2 := gaussian_cos_integrable (2 * t)
  unfold p3EvenMoment p3Argument
  calc
    (∫ G : ℝ, Real.cos (Real.sqrt ((13 / 4 : ℝ) / 3) * G) ^ (2 * 1)
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ, (1 : ℝ) / 2 + (1 / 2 : ℝ) *
          Real.cos ((2 * t) * G) ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      simpa [t, p3Argument, sq_abs, mul_assoc] using cos_two_identity
        (Real.sqrt ((13 / 4 : ℝ) / 3) * G)
    _ = (1 : ℝ) / 2 + (1 / 2 : ℝ) *
          Real.exp (-(2 * t) ^ 2 / 2) := by
      rw [integral_add h0 (h2.const_mul (1 / 2 : ℝ)), integral_const,
        integral_const_mul, gaussian_cosine_charFun]
      simp
    _ = (1 : ℝ) / 2 + (1 / 2 : ℝ) * Real.exp (-(13 : ℝ) / 6) := by
      have h2exp : -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 6 := by
        nlinarith [ht]
      rw [h2exp]

/-- Exact Gaussian evaluation of the fourth cosine moment. -/
theorem p3_even_moment_two :
    p3EvenMoment 2 =
      (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
        (1 / 8 : ℝ) * Real.exp (-(26 : ℝ) / 3) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 3)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 3 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have hpoint (G : ℝ) :
      Real.cos (p3Argument G) ^ (2 * 2) =
        (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
          (1 / 8 : ℝ) * Real.cos ((4 * t) * G) := by
    calc
      Real.cos (p3Argument G) ^ (2 * 2) =
          |Real.cos (p3Argument G)| ^ (2 * 2) :=
        (abs_pow_even (Real.cos (p3Argument G)) 2).symm
      _ = (3 : ℝ) / 8 + (1 / 2 : ℝ) *
          Real.cos (2 * p3Argument G) +
            (1 / 8 : ℝ) * Real.cos (4 * p3Argument G) := by
        simpa only [show 2 * 2 = 4 by norm_num] using
          cos_four_identity (p3Argument G)
      _ = (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
          (1 / 8 : ℝ) * Real.cos ((4 * t) * G) := by
        have harg : p3Argument G = t * G := by
          rfl
        rw [harg]
        congr 2 <;> ring
  unfold p3EvenMoment
  calc
    (∫ G : ℝ, Real.cos (p3Argument G) ^ (2 * 2)
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.cos ((2 * t) * G) +
            (1 / 8 : ℝ) * Real.cos ((4 * t) * G)
          ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ = (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (1 / 8 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) :=
      gaussian_integral_fourier4 t
    _ = (3 : ℝ) / 8 + (1 / 2 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
          (1 / 8 : ℝ) * Real.exp (-(26 : ℝ) / 3) := by
      rw [show -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 6 by nlinarith [ht],
        show -(4 * t) ^ 2 / 2 = -(26 : ℝ) / 3 by nlinarith [ht]]

/-- Exact Gaussian evaluation of the sixth cosine moment. -/
theorem p3_even_moment_three :
    p3EvenMoment 3 =
      (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
        (6 / 32 : ℝ) * Real.exp (-(26 : ℝ) / 3) +
          (1 / 32 : ℝ) * Real.exp (-(39 : ℝ) / 2) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 3)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 3 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have hpoint (G : ℝ) :
      Real.cos (p3Argument G) ^ (2 * 3) =
        (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
          (6 / 32 : ℝ) * Real.cos ((4 * t) * G) +
            (1 / 32 : ℝ) * Real.cos ((6 * t) * G) := by
    calc
      Real.cos (p3Argument G) ^ (2 * 3) =
          |Real.cos (p3Argument G)| ^ (2 * 3) :=
        (abs_pow_even (Real.cos (p3Argument G)) 3).symm
      _ = (10 : ℝ) / 32 + (15 / 32 : ℝ) *
          Real.cos (2 * p3Argument G) +
            (6 / 32 : ℝ) * Real.cos (4 * p3Argument G) +
              (1 / 32 : ℝ) * Real.cos (6 * p3Argument G) := by
        simpa only [show 2 * 3 = 6 by norm_num] using
          cos_six_identity (p3Argument G)
      _ = (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
          (6 / 32 : ℝ) * Real.cos ((4 * t) * G) +
            (1 / 32 : ℝ) * Real.cos ((6 * t) * G) := by
        have harg : p3Argument G = t * G := by
          rfl
        rw [harg]
        congr 2 <;> ring
  unfold p3EvenMoment
  calc
    (∫ G : ℝ, Real.cos (p3Argument G) ^ (2 * 3)
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.cos ((2 * t) * G) +
            (6 / 32 : ℝ) * Real.cos ((4 * t) * G) +
              (1 / 32 : ℝ) * Real.cos ((6 * t) * G)
          ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ = (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (6 / 32 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (1 / 32 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) :=
      gaussian_integral_fourier6 t
    _ = (10 : ℝ) / 32 + (15 / 32 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
          (6 / 32 : ℝ) * Real.exp (-(26 : ℝ) / 3) +
            (1 / 32 : ℝ) * Real.exp (-(39 : ℝ) / 2) := by
      rw [show -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 6 by nlinarith [ht],
        show -(4 * t) ^ 2 / 2 = -(26 : ℝ) / 3 by nlinarith [ht],
        show -(6 * t) ^ 2 / 2 = -(39 : ℝ) / 2 by nlinarith [ht]]

/-- Exact Gaussian evaluation of the eighth cosine moment. -/
theorem p3_even_moment_four :
    p3EvenMoment 4 =
      (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
        (28 / 128 : ℝ) * Real.exp (-(26 : ℝ) / 3) +
          (8 / 128 : ℝ) * Real.exp (-(39 : ℝ) / 2) +
            (1 / 128 : ℝ) * Real.exp (-(104 : ℝ) / 3) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 3)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 3 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have hpoint (G : ℝ) :
      Real.cos (p3Argument G) ^ (2 * 4) =
        (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
          (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
            (8 / 128 : ℝ) * Real.cos ((6 * t) * G) +
              (1 / 128 : ℝ) * Real.cos ((8 * t) * G) := by
    calc
      Real.cos (p3Argument G) ^ (2 * 4) =
          |Real.cos (p3Argument G)| ^ (2 * 4) :=
        (abs_pow_even (Real.cos (p3Argument G)) 4).symm
      _ = (35 : ℝ) / 128 + (56 / 128 : ℝ) *
          Real.cos (2 * p3Argument G) +
            (28 / 128 : ℝ) * Real.cos (4 * p3Argument G) +
              (8 / 128 : ℝ) * Real.cos (6 * p3Argument G) +
                (1 / 128 : ℝ) * Real.cos (8 * p3Argument G) := by
        simpa only [show 2 * 4 = 8 by norm_num] using
          cos_eight_identity (p3Argument G)
      _ = (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.cos ((2 * t) * G) +
          (28 / 128 : ℝ) * Real.cos ((4 * t) * G) +
            (8 / 128 : ℝ) * Real.cos ((6 * t) * G) +
              (1 / 128 : ℝ) * Real.cos ((8 * t) * G) := by
        have harg : p3Argument G = t * G := by
          rfl
        rw [harg]
        congr 2 <;> ring
  unfold p3EvenMoment
  calc
    (∫ G : ℝ, Real.cos (p3Argument G) ^ (2 * 4)
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
    _ = (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (28 / 128 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (8 / 128 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
              (1 / 128 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) :=
      gaussian_integral_fourier8 t
    _ = (35 : ℝ) / 128 + (56 / 128 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
          (28 / 128 : ℝ) * Real.exp (-(26 : ℝ) / 3) +
            (8 / 128 : ℝ) * Real.exp (-(39 : ℝ) / 2) +
              (1 / 128 : ℝ) * Real.exp (-(104 : ℝ) / 3) := by
      rw [show -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 6 by nlinarith [ht],
        show -(4 * t) ^ 2 / 2 = -(26 : ℝ) / 3 by nlinarith [ht],
        show -(6 * t) ^ 2 / 2 = -(39 : ℝ) / 2 by nlinarith [ht],
        show -(8 * t) ^ 2 / 2 = -(104 : ℝ) / 3 by nlinarith [ht]]

/-- Exact Gaussian evaluation of the tenth cosine moment. -/
theorem p3_even_moment_five :
    p3EvenMoment 5 =
      (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
        (120 / 512 : ℝ) * Real.exp (-(26 : ℝ) / 3) +
          (45 / 512 : ℝ) * Real.exp (-(39 : ℝ) / 2) +
            (10 / 512 : ℝ) * Real.exp (-(104 : ℝ) / 3) +
              (1 / 512 : ℝ) * Real.exp (-(325 : ℝ) / 6) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 3)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 3 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have hpoint (G : ℝ) :
      Real.cos (p3Argument G) ^ (2 * 5) =
        (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.cos ((2 * t) * G) +
          (120 / 512 : ℝ) * Real.cos ((4 * t) * G) +
            (45 / 512 : ℝ) * Real.cos ((6 * t) * G) +
              (10 / 512 : ℝ) * Real.cos ((8 * t) * G) +
                (1 / 512 : ℝ) * Real.cos ((10 * t) * G) := by
    calc
      Real.cos (p3Argument G) ^ (2 * 5) =
          |Real.cos (p3Argument G)| ^ (2 * 5) :=
        (abs_pow_even (Real.cos (p3Argument G)) 5).symm
      _ = (126 : ℝ) / 512 + (210 / 512 : ℝ) *
          Real.cos (2 * p3Argument G) +
            (120 / 512 : ℝ) * Real.cos (4 * p3Argument G) +
              (45 / 512 : ℝ) * Real.cos (6 * p3Argument G) +
                (10 / 512 : ℝ) * Real.cos (8 * p3Argument G) +
                  (1 / 512 : ℝ) * Real.cos (10 * p3Argument G) := by
        simpa only [show 2 * 5 = 10 by norm_num] using
          cos_ten_identity (p3Argument G)
      _ = (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.cos ((2 * t) * G) +
          (120 / 512 : ℝ) * Real.cos ((4 * t) * G) +
            (45 / 512 : ℝ) * Real.cos ((6 * t) * G) +
              (10 / 512 : ℝ) * Real.cos ((8 * t) * G) +
                (1 / 512 : ℝ) * Real.cos ((10 * t) * G) := by
        have harg : p3Argument G = t * G := by rfl
        rw [harg]
        congr 2 <;> ring
  unfold p3EvenMoment
  calc
    (∫ G : ℝ, Real.cos (p3Argument G) ^ (2 * 5)
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.cos ((2 * t) * G) +
            (120 / 512 : ℝ) * Real.cos ((4 * t) * G) +
              (45 / 512 : ℝ) * Real.cos ((6 * t) * G) +
                (10 / 512 : ℝ) * Real.cos ((8 * t) * G) +
                  (1 / 512 : ℝ) * Real.cos ((10 * t) * G)
          ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ = (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (120 / 512 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (45 / 512 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
              (10 / 512 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) +
                (1 / 512 : ℝ) * Real.exp (-(10 * t) ^ 2 / 2) :=
      gaussian_integral_fourier10 t
    _ = (126 : ℝ) / 512 + (210 / 512 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
          (120 / 512 : ℝ) * Real.exp (-(26 : ℝ) / 3) +
            (45 / 512 : ℝ) * Real.exp (-(39 : ℝ) / 2) +
              (10 / 512 : ℝ) * Real.exp (-(104 : ℝ) / 3) +
                (1 / 512 : ℝ) * Real.exp (-(325 : ℝ) / 6) := by
      rw [show -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 6 by nlinarith [ht],
        show -(4 * t) ^ 2 / 2 = -(26 : ℝ) / 3 by nlinarith [ht],
        show -(6 * t) ^ 2 / 2 = -(39 : ℝ) / 2 by nlinarith [ht],
        show -(8 * t) ^ 2 / 2 = -(104 : ℝ) / 3 by nlinarith [ht],
        show -(10 * t) ^ 2 / 2 = -(325 : ℝ) / 6 by nlinarith [ht]]

/-- Exact Gaussian evaluation of the twelfth cosine moment. -/
theorem p3_even_moment_six :
    p3EvenMoment 6 =
      (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
        (495 / 2048 : ℝ) * Real.exp (-(26 : ℝ) / 3) +
          (220 / 2048 : ℝ) * Real.exp (-(39 : ℝ) / 2) +
            (66 / 2048 : ℝ) * Real.exp (-(104 : ℝ) / 3) +
              (12 / 2048 : ℝ) * Real.exp (-(325 : ℝ) / 6) +
                (1 / 2048 : ℝ) * Real.exp (-78) := by
  let t : ℝ := Real.sqrt ((13 / 4 : ℝ) / 3)
  have ht : t ^ 2 = (13 / 4 : ℝ) / 3 := by
    dsimp [t]
    apply Real.sq_sqrt
    norm_num
  have hpoint (G : ℝ) :
      Real.cos (p3Argument G) ^ (2 * 6) =
        (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.cos ((2 * t) * G) +
          (495 / 2048 : ℝ) * Real.cos ((4 * t) * G) +
            (220 / 2048 : ℝ) * Real.cos ((6 * t) * G) +
              (66 / 2048 : ℝ) * Real.cos ((8 * t) * G) +
                (12 / 2048 : ℝ) * Real.cos ((10 * t) * G) +
                  (1 / 2048 : ℝ) * Real.cos ((12 * t) * G) := by
    calc
      Real.cos (p3Argument G) ^ (2 * 6) =
          |Real.cos (p3Argument G)| ^ (2 * 6) :=
        (abs_pow_even (Real.cos (p3Argument G)) 6).symm
      _ = (462 : ℝ) / 2048 + (792 / 2048 : ℝ) *
          Real.cos (2 * p3Argument G) +
            (495 / 2048 : ℝ) * Real.cos (4 * p3Argument G) +
              (220 / 2048 : ℝ) * Real.cos (6 * p3Argument G) +
                (66 / 2048 : ℝ) * Real.cos (8 * p3Argument G) +
                  (12 / 2048 : ℝ) * Real.cos (10 * p3Argument G) +
                    (1 / 2048 : ℝ) * Real.cos (12 * p3Argument G) := by
        simpa only [show 2 * 6 = 12 by norm_num] using
          cos_twelve_identity (p3Argument G)
      _ = (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.cos ((2 * t) * G) +
          (495 / 2048 : ℝ) * Real.cos ((4 * t) * G) +
            (220 / 2048 : ℝ) * Real.cos ((6 * t) * G) +
              (66 / 2048 : ℝ) * Real.cos ((8 * t) * G) +
                (12 / 2048 : ℝ) * Real.cos ((10 * t) * G) +
                  (1 / 2048 : ℝ) * Real.cos ((12 * t) * G) := by
        have harg : p3Argument G = t * G := by rfl
        rw [harg]
        congr 2 <;> ring
  unfold p3EvenMoment
  calc
    (∫ G : ℝ, Real.cos (p3Argument G) ^ (2 * 6)
        ∂(gaussianReal 0 1)) =
        ∫ G : ℝ,
          (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.cos ((2 * t) * G) +
            (495 / 2048 : ℝ) * Real.cos ((4 * t) * G) +
              (220 / 2048 : ℝ) * Real.cos ((6 * t) * G) +
                (66 / 2048 : ℝ) * Real.cos ((8 * t) * G) +
                  (12 / 2048 : ℝ) * Real.cos ((10 * t) * G) +
                    (1 / 2048 : ℝ) * Real.cos ((12 * t) * G)
          ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ = (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.exp (-(2 * t) ^ 2 / 2) +
          (495 / 2048 : ℝ) * Real.exp (-(4 * t) ^ 2 / 2) +
            (220 / 2048 : ℝ) * Real.exp (-(6 * t) ^ 2 / 2) +
              (66 / 2048 : ℝ) * Real.exp (-(8 * t) ^ 2 / 2) +
                (12 / 2048 : ℝ) * Real.exp (-(10 * t) ^ 2 / 2) +
                  (1 / 2048 : ℝ) * Real.exp (-(12 * t) ^ 2 / 2) :=
      gaussian_integral_fourier12 t
    _ = (462 : ℝ) / 2048 + (792 / 2048 : ℝ) * Real.exp (-(13 : ℝ) / 6) +
          (495 / 2048 : ℝ) * Real.exp (-(26 : ℝ) / 3) +
            (220 / 2048 : ℝ) * Real.exp (-(39 : ℝ) / 2) +
              (66 / 2048 : ℝ) * Real.exp (-(104 : ℝ) / 3) +
                (12 / 2048 : ℝ) * Real.exp (-(325 : ℝ) / 6) +
                  (1 / 2048 : ℝ) * Real.exp (-78) := by
      rw [show -(2 * t) ^ 2 / 2 = -(13 : ℝ) / 6 by nlinarith [ht],
        show -(4 * t) ^ 2 / 2 = -(26 : ℝ) / 3 by nlinarith [ht],
        show -(6 * t) ^ 2 / 2 = -(39 : ℝ) / 2 by nlinarith [ht],
        show -(8 * t) ^ 2 / 2 = -(104 : ℝ) / 3 by nlinarith [ht],
        show -(10 * t) ^ 2 / 2 = -(325 : ℝ) / 6 by nlinarith [ht],
        show -(12 * t) ^ 2 / 2 = (-78 : ℝ) by nlinarith [ht]]

/-- Degree-six polynomial majorant in the variable `u = cos² x`. -/
def p3Majorant (u : ℝ) : ℝ :=
  (14283 : ℝ) / 85750 * u + (153323 / 85750 : ℝ) * u ^ 2 -
    (2769016 / 1157625 : ℝ) * u ^ 3 +
      (1040968 / 385875 : ℝ) * u ^ 4 -
        (93952 / 55125 : ℝ) * u ^ 5 +
          (514048 / 1157625 : ℝ) * u ^ 6

/-- The majorant defect factors into squared contacts and a positive polynomial. -/
theorem p3Majorant_sub_factorization (t : ℝ) :
    p3Majorant (t ^ 2) - t ^ 3 =
      t ^ 2 * (1 - t) ^ 2 * (t - 1 / 2) ^ 2 * (t - 3 / 4) ^ 2 *
        ((50784 : ℝ) / 42875 + (1217152 / 385875 : ℝ) * t +
          (4163456 / 1157625 : ℝ) * t ^ 2 +
            (257024 / 128625 : ℝ) * t ^ 3 +
              (514048 / 1157625 : ℝ) * t ^ 4) := by
  dsimp [p3Majorant]
  ring

/-- The majorant dominates `t³` for every nonnegative `t`. -/
theorem p3Majorant_pointwise {t : ℝ} (ht0 : 0 ≤ t) :
    t ^ 3 ≤ p3Majorant (t ^ 2) := by
  rw [← sub_nonneg]
  rw [p3Majorant_sub_factorization]
  positivity

/-- The dense p=3 scalar moment is bounded by the six exact even moments. -/
theorem sparseScalarF_13_div_4_three_le_even_majorant :
    sparseScalarF (13 / 4) 3 ≤
      (14283 : ℝ) / 85750 * p3EvenMoment 1 +
        (153323 / 85750 : ℝ) * p3EvenMoment 2 -
          (2769016 / 1157625 : ℝ) * p3EvenMoment 3 +
            (1040968 / 385875 : ℝ) * p3EvenMoment 4 -
              (93952 / 55125 : ℝ) * p3EvenMoment 5 +
                (514048 / 1157625 : ℝ) * p3EvenMoment 6 := by
  have hpoint (G : ℝ) :
      sparseScalarFIntegrand (13 / 4) 3 G ≤
        p3Majorant ((Real.cos (p3Argument G)) ^ 2) := by
    dsimp [sparseScalarFIntegrand, p3Argument]
    calc
      Real.rpow
          |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 3) * G)| (3 : ℝ) =
          |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 3) * G)| ^ (3 : ℕ) :=
        Real.rpow_natCast _ 3
      _ ≤ p3Majorant
          (Real.cos (Real.sqrt ((13 / 4 : ℝ) / 3) * G) ^ 2) := by
        simpa [sq_abs] using
          (p3Majorant_pointwise (t :=
            |Real.cos (Real.sqrt ((13 / 4 : ℝ) / 3) * G)|)
            (by positivity))
  have hleft := sparseScalarF_integrable (s := (13 / 4 : ℝ)) (p := 3) (by norm_num)
  have hmom (n : ℕ) :
      Integrable (fun G : ℝ => Real.cos (p3Argument G) ^ (2 * n))
        (gaussianReal 0 1) := by
    simpa [p3Argument] using
      gaussian_cos_power_integrable (Real.sqrt ((13 / 4 : ℝ) / 3)) (2 * n)
  have hright : Integrable (fun G : ℝ =>
      p3Majorant ((Real.cos (p3Argument G)) ^ 2))
      (gaussianReal 0 1) := by
    have h1 : Integrable (fun G : ℝ =>
        (14283 : ℝ) / 85750 * Real.cos (p3Argument G) ^ 2)
        (gaussianReal 0 1) := (hmom 1).const_mul _
    have h2 : Integrable (fun G : ℝ =>
        (153323 : ℝ) / 85750 * Real.cos (p3Argument G) ^ 4)
        (gaussianReal 0 1) := (hmom 2).const_mul _
    have h3 : Integrable (fun G : ℝ =>
        (2769016 : ℝ) / 1157625 * Real.cos (p3Argument G) ^ 6)
        (gaussianReal 0 1) := (hmom 3).const_mul _
    have h4 : Integrable (fun G : ℝ =>
        (1040968 : ℝ) / 385875 * Real.cos (p3Argument G) ^ 8)
        (gaussianReal 0 1) := (hmom 4).const_mul _
    have h5 : Integrable (fun G : ℝ =>
        (93952 : ℝ) / 55125 * Real.cos (p3Argument G) ^ 10)
        (gaussianReal 0 1) := (hmom 5).const_mul _
    have h6 : Integrable (fun G : ℝ =>
        (514048 : ℝ) / 1157625 * Real.cos (p3Argument G) ^ 12)
        (gaussianReal 0 1) := (hmom 6).const_mul _
    have hfun : (fun G : ℝ => p3Majorant ((Real.cos (p3Argument G)) ^ 2)) =
        (((((fun G : ℝ => (14283 : ℝ) / 85750 *
          Real.cos (p3Argument G) ^ 2) +
          (fun G : ℝ => (153323 : ℝ) / 85750 *
            Real.cos (p3Argument G) ^ 4)) -
          (fun G : ℝ => (2769016 : ℝ) / 1157625 *
            Real.cos (p3Argument G) ^ 6)) +
          (fun G : ℝ => (1040968 : ℝ) / 385875 *
            Real.cos (p3Argument G) ^ 8)) -
          (fun G : ℝ => (93952 : ℝ) / 55125 *
            Real.cos (p3Argument G) ^ 10)) +
          (fun G : ℝ => (514048 : ℝ) / 1157625 *
            Real.cos (p3Argument G) ^ 12) := by
      funext G
      dsimp [p3Majorant]
      ring
    rw [hfun]
    exact (((((h1.add h2).sub h3).add h4).sub h5).add h6)
  have hmono := integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
  unfold sparseScalarF at hmono ⊢
  calc
    (∫ G : ℝ, sparseScalarFIntegrand (13 / 4) 3 G ∂(gaussianReal 0 1)) ≤
        ∫ G : ℝ, p3Majorant ((Real.cos (p3Argument G)) ^ 2)
          ∂(gaussianReal 0 1) := hmono
    _ = (14283 : ℝ) / 85750 * p3EvenMoment 1 +
          (153323 / 85750 : ℝ) * p3EvenMoment 2 -
            (2769016 / 1157625 : ℝ) * p3EvenMoment 3 +
              (1040968 / 385875 : ℝ) * p3EvenMoment 4 -
                (93952 / 55125 : ℝ) * p3EvenMoment 5 +
                  (514048 / 1157625 : ℝ) * p3EvenMoment 6 := by
      have h1 : Integrable (fun G : ℝ =>
          (14283 : ℝ) / 85750 * Real.cos (p3Argument G) ^ 2)
          (gaussianReal 0 1) := (hmom 1).const_mul _
      have h2 : Integrable (fun G : ℝ =>
          (153323 : ℝ) / 85750 * Real.cos (p3Argument G) ^ 4)
          (gaussianReal 0 1) := (hmom 2).const_mul _
      have h3 : Integrable (fun G : ℝ =>
          (2769016 : ℝ) / 1157625 * Real.cos (p3Argument G) ^ 6)
          (gaussianReal 0 1) := (hmom 3).const_mul _
      have h4 : Integrable (fun G : ℝ =>
          (1040968 : ℝ) / 385875 * Real.cos (p3Argument G) ^ 8)
          (gaussianReal 0 1) := (hmom 4).const_mul _
      have h5 : Integrable (fun G : ℝ =>
          (93952 : ℝ) / 55125 * Real.cos (p3Argument G) ^ 10)
          (gaussianReal 0 1) := (hmom 5).const_mul _
      have h6 : Integrable (fun G : ℝ =>
          (514048 : ℝ) / 1157625 * Real.cos (p3Argument G) ^ 12)
          (gaussianReal 0 1) := (hmom 6).const_mul _
      calc
        (∫ G : ℝ, p3Majorant ((Real.cos (p3Argument G)) ^ 2)
            ∂(gaussianReal 0 1)) =
            ∫ G : ℝ,
              (14283 : ℝ) / 85750 * Real.cos (p3Argument G) ^ 2 +
                (153323 : ℝ) / 85750 * Real.cos (p3Argument G) ^ 4 -
                  (2769016 : ℝ) / 1157625 * Real.cos (p3Argument G) ^ 6 +
                    (1040968 : ℝ) / 385875 * Real.cos (p3Argument G) ^ 8 -
                      (93952 : ℝ) / 55125 * Real.cos (p3Argument G) ^ 10 +
                        (514048 : ℝ) / 1157625 * Real.cos (p3Argument G) ^ 12
              ∂(gaussianReal 0 1) := by
          apply integral_congr_ae
          filter_upwards [] with G
          dsimp [p3Majorant]
          ring
        _ = (∫ G : ℝ, (14283 : ℝ) / 85750 *
              Real.cos (p3Argument G) ^ 2 ∂(gaussianReal 0 1)) +
              (∫ G : ℝ, (153323 : ℝ) / 85750 *
                Real.cos (p3Argument G) ^ 4 ∂(gaussianReal 0 1)) -
              (∫ G : ℝ, (2769016 : ℝ) / 1157625 *
                Real.cos (p3Argument G) ^ 6 ∂(gaussianReal 0 1)) +
              (∫ G : ℝ, (1040968 : ℝ) / 385875 *
                Real.cos (p3Argument G) ^ 8 ∂(gaussianReal 0 1)) -
              (∫ G : ℝ, (93952 : ℝ) / 55125 *
                Real.cos (p3Argument G) ^ 10 ∂(gaussianReal 0 1)) +
              (∫ G : ℝ, (514048 : ℝ) / 1157625 *
                Real.cos (p3Argument G) ^ 12 ∂(gaussianReal 0 1)) := by
          exact integral_six_linear h1 h2 h3 h4 h5 h6
        _ = (14283 : ℝ) / 85750 * p3EvenMoment 1 +
              (153323 / 85750 : ℝ) * p3EvenMoment 2 -
                (2769016 / 1157625 : ℝ) * p3EvenMoment 3 +
                  (1040968 / 385875 : ℝ) * p3EvenMoment 4 -
                    (93952 / 55125 : ℝ) * p3EvenMoment 5 +
                      (514048 / 1157625 : ℝ) * p3EvenMoment 6 := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul,
            integral_const_mul, integral_const_mul, integral_const_mul]
          rfl

end DenseScalar
end CertifiedProjections
