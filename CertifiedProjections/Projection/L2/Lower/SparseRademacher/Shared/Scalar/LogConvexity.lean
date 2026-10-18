/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.Interpolation
import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.Moment
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Multiplicative scalar interpolation

This module is the L5 boundary after the exact `F_s`/`I_s` change of
variables.  It proves the multiplicative log-convexity producer for `I_s`
without taking logarithms.  Strict positivity is retained in the hypotheses,
so the later logarithmic statement cannot use totalized `Real.log` at zero.
-/

open scoped ENNReal

open MeasureTheory

namespace CertifiedProjections

/-- Pointwise `Real.rpow` interpolation for the scalar lobe integrand. -/
theorem scalarLobeIntegrand_interpolate {s a b p θ y : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : p = (1 - θ) * a + θ * b) :
    scalarLobeIntegrand s p y =
      scalarLobeIntegrand s a y ^ (1 - θ) *
        scalarLobeIntegrand s b y ^ θ := by
  have hbase : 0 ≤ Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y| :=
    mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hθa : 0 ≤ (1 - θ) * a :=
    mul_nonneg (sub_nonneg.mpr hθ1) ha.le
  have hθb : 0 ≤ θ * b := mul_nonneg hθ0 hb.le
  unfold scalarLobeIntegrand
  calc
    Real.rpow (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|) p =
        Real.rpow (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|)
          ((1 - θ) * a + θ * b) := by rw [hp]
    _ = Real.rpow (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|)
          ((1 - θ) * a) *
        Real.rpow (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|) (θ * b) :=
      Real.rpow_add_of_nonneg hbase hθa hθb
    _ = (Real.rpow (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|) a) ^
          (1 - θ) *
        (Real.rpow (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|) b) ^ θ := by
      congr 1
      · simpa [mul_comm] using (Real.rpow_mul hbase a (1 - θ))
      · simpa [mul_comm] using (Real.rpow_mul hbase b θ)

private noncomputable def scalarLobeBase (s : ℝ) : ℝ → ℝ≥0∞ :=
  fun y => ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|)

private lemma scalarLobeBase_nonneg {s y : ℝ} :
    0 ≤ Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y| := by
  exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)

private lemma scalarLobeBase_aemeasurable {s : ℝ} :
    AEMeasurable (scalarLobeBase s) volume := by
  change AEMeasurable
    (fun y => ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y|)) volume
  fun_prop

private lemma scalarLobeIntegrand_nonneg' {s r y : ℝ} :
    0 ≤ scalarLobeIntegrand s r y := by
  exact Real.rpow_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) _

private lemma scalarLobeBase_integral_rpow {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    ENNReal.ofReal (scalarLobeIntegral s r) =
      ∫⁻ y : ℝ, scalarLobeBase s y ^ r := by
  rw [scalarLobeIntegral]
  rw [ofReal_integral_eq_lintegral_ofReal
    (scalarLobeIntegrand_integrable hs hr)]
  · apply lintegral_congr_ae
    filter_upwards [] with y
    dsimp [scalarLobeBase, scalarLobeIntegrand]
    exact (ENNReal.ofReal_rpow_of_nonneg
      (scalarLobeBase_nonneg (s := s) (y := y)) hr.le).symm
  · filter_upwards [] with y
    exact scalarLobeIntegrand_nonneg'

private lemma scalarLobeBase_interpolate {s a b p θ y : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : p = (1 - θ) * a + θ * b) :
    (scalarLobeBase s y ^ a) ^ (1 - θ) *
        (scalarLobeBase s y ^ b) ^ θ =
      scalarLobeBase s y ^ p := by
  have hθa : 0 ≤ (1 - θ) * a :=
    mul_nonneg (sub_nonneg.mpr hθ1) ha.le
  have hθb : 0 ≤ θ * b := mul_nonneg hθ0 hb.le
  have hθa' : 0 ≤ a * (1 - θ) := by simpa [mul_comm] using hθa
  have hθb' : 0 ≤ b * θ := by simpa [mul_comm] using hθb
  calc
    (scalarLobeBase s y ^ a) ^ (1 - θ) *
          (scalarLobeBase s y ^ b) ^ θ =
        scalarLobeBase s y ^ (a * (1 - θ)) *
          scalarLobeBase s y ^ (b * θ) := by
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    _ = scalarLobeBase s y ^ (a * (1 - θ) + b * θ) :=
      (ENNReal.rpow_add_of_nonneg (a * (1 - θ)) (b * θ) hθa' hθb').symm
    _ = scalarLobeBase s y ^ p := by
      rw [hp]
      congr 1
      ring

/-- Multiplicative log-convexity of `I_s` on a positive interpolation
interval.  This is the Hölder producer used by the later L5 logarithmic
statement. -/
theorem scalarLobeIntegral_mul_rpow_le {s a b p θ : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (hp0 : 0 < p)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : p = (1 - θ) * a + θ * b) :
    scalarLobeIntegral s p ≤
      scalarLobeIntegral s a ^ (1 - θ) * scalarLobeIntegral s b ^ θ := by
  let B : ℝ → ℝ≥0∞ := scalarLobeBase s
  have hB : AEMeasurable B volume := by
    exact scalarLobeBase_aemeasurable
  have hholder :
      (∫⁻ y : ℝ, (B y ^ a) ^ (1 - θ) * (B y ^ b) ^ θ) ≤
        (∫⁻ y : ℝ, B y ^ a) ^ (1 - θ) *
          (∫⁻ y : ℝ, B y ^ b) ^ θ := by
    exact ENNReal.lintegral_mul_norm_pow_le
      (hB.pow_const a) (hB.pow_const b)
      (sub_nonneg.mpr hθ1) hθ0 (by ring)
  have hleft :
      ENNReal.ofReal (scalarLobeIntegral s p) =
        ∫⁻ y : ℝ, (B y ^ a) ^ (1 - θ) * (B y ^ b) ^ θ := by
    rw [scalarLobeBase_integral_rpow hs hp0]
    apply lintegral_congr_ae
    filter_upwards [] with y
    exact (scalarLobeBase_interpolate ha hb hθ0 hθ1 hp).symm
  have hright :
      (∫⁻ y : ℝ, B y ^ a) ^ (1 - θ) *
          (∫⁻ y : ℝ, B y ^ b) ^ θ =
        ENNReal.ofReal (scalarLobeIntegral s a) ^ (1 - θ) *
          ENNReal.ofReal (scalarLobeIntegral s b) ^ θ := by
    rw [← scalarLobeBase_integral_rpow hs ha,
      ← scalarLobeBase_integral_rpow hs hb]
  have henn :
      ENNReal.ofReal (scalarLobeIntegral s p) ≤
        ENNReal.ofReal (scalarLobeIntegral s a) ^ (1 - θ) *
          ENNReal.ofReal (scalarLobeIntegral s b) ^ θ := by
    rw [hleft, ← hright]
    exact hholder
  have hIa : 0 ≤ scalarLobeIntegral s a :=
    (scalarLobeIntegral_pos hs ha).le
  have hIb : 0 ≤ scalarLobeIntegral s b :=
    (scalarLobeIntegral_pos hs hb).le
  have hθa' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hθb' : 0 ≤ θ := hθ0
  have hprod :
      0 ≤ scalarLobeIntegral s a ^ (1 - θ) *
        scalarLobeIntegral s b ^ θ :=
    mul_nonneg (Real.rpow_nonneg hIa _) (Real.rpow_nonneg hIb _)
  have henn_real :
      ENNReal.ofReal (scalarLobeIntegral s p) ≤
        ENNReal.ofReal
          (scalarLobeIntegral s a ^ (1 - θ) *
            scalarLobeIntegral s b ^ θ) := by
    have hconvert :
        ENNReal.ofReal
            (scalarLobeIntegral s a ^ (1 - θ) *
              scalarLobeIntegral s b ^ θ) =
          ENNReal.ofReal (scalarLobeIntegral s a) ^ (1 - θ) *
            ENNReal.ofReal (scalarLobeIntegral s b) ^ θ := by
      calc
        ENNReal.ofReal
            (scalarLobeIntegral s a ^ (1 - θ) *
              scalarLobeIntegral s b ^ θ) =
            ENNReal.ofReal (scalarLobeIntegral s a ^ (1 - θ)) *
              ENNReal.ofReal (scalarLobeIntegral s b ^ θ) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg hIa _)
        _ = ENNReal.ofReal (scalarLobeIntegral s a) ^ (1 - θ) *
              ENNReal.ofReal (scalarLobeIntegral s b) ^ θ := by
          rw [ENNReal.ofReal_rpow_of_nonneg hIa hθa',
            ENNReal.ofReal_rpow_of_nonneg hIb hθb']
    rw [hconvert]
    exact henn
  exact (ENNReal.ofReal_le_ofReal_iff hprod).mp henn_real

private lemma scalarLobeIntegral_log_eq_interpolated_bound {s a b p θ : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) (_hab : a < b)
    (hp0 : 0 < p)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : p = (1 - θ) * a + θ * b) :
    Real.log (scalarLobeIntegral s p) ≤
      (1 - θ) * Real.log (scalarLobeIntegral s a) +
        θ * Real.log (scalarLobeIntegral s b) := by
  have hIa : 0 < scalarLobeIntegral s a := scalarLobeIntegral_pos hs ha
  have hIb : 0 < scalarLobeIntegral s b := scalarLobeIntegral_pos hs hb
  have hmul := scalarLobeIntegral_mul_rpow_le
    hs ha hb hp0 hθ0 hθ1 hp
  have hlog := Real.log_le_log (scalarLobeIntegral_pos hs hp0) hmul
  rw [Real.log_mul (Real.rpow_pos_of_pos hIa _).ne'
      (Real.rpow_pos_of_pos hIb _).ne',
    Real.log_rpow hIa, Real.log_rpow hIb] at hlog
  exact hlog

private lemma sparseScalarF_log_eq_lobe {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    Real.log (sparseScalarF s r) =
      (1 / 2 : ℝ) *
          (Real.log r - Real.log (2 * Real.pi * s)) +
        Real.log (scalarLobeIntegral s r) := by
  rw [sparseScalarF_eq_sqrt_mul_scalarLobeIntegral hs hr]
  rw [Real.log_mul (by positivity)
      (scalarLobeIntegral_pos hs hr).ne', Real.log_sqrt (by positivity)]
  rw [Real.log_div hr.ne' (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  ring

/-- The paper-facing logarithmic L5 interpolation inequality, with the
positive correction `+ 1/2 * (log p - weighted endpoint logs)`. -/
theorem sparseScalarF_log_interpolation {s a b p θ : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hp0 : 0 < p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : p = (1 - θ) * a + θ * b) :
    Real.log (sparseScalarF s p) ≤
      (1 - θ) * Real.log (sparseScalarF s a) +
        θ * Real.log (sparseScalarF s b) +
          (1 / 2 : ℝ) *
            (Real.log p - (1 - θ) * Real.log a - θ * Real.log b) := by
  have hlogI := scalarLobeIntegral_log_eq_interpolated_bound
    hs ha hb hab hp0 hθ0 hθ1 hp
  calc
    Real.log (sparseScalarF s p) =
        (1 / 2 : ℝ) *
            (Real.log p - Real.log (2 * Real.pi * s)) +
          Real.log (scalarLobeIntegral s p) :=
      sparseScalarF_log_eq_lobe hs hp0
    _ ≤ (1 / 2 : ℝ) *
          (Real.log p - Real.log (2 * Real.pi * s)) +
        ((1 - θ) * Real.log (scalarLobeIntegral s a) +
          θ * Real.log (scalarLobeIntegral s b)) :=
      by simpa [add_comm] using
        (add_le_add_right hlogI
          ((1 / 2 : ℝ) * (Real.log p - Real.log (2 * Real.pi * s))))
    _ = (1 - θ) * Real.log (sparseScalarF s a) +
          θ * Real.log (sparseScalarF s b) +
            (1 / 2 : ℝ) *
              (Real.log p - (1 - θ) * Real.log a - θ * Real.log b) := by
      rw [sparseScalarF_log_eq_lobe hs ha,
        sparseScalarF_log_eq_lobe hs hb]
      ring

private lemma sparseScalarF_log_rhs {s a b p θ : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) (hp0 : 0 < p)
    :
    Real.log
        (sparseScalarF s a ^ (1 - θ) *
          sparseScalarF s b ^ θ *
            Real.sqrt (p /
              (a ^ (1 - θ) * b ^ θ))) =
      (1 - θ) * Real.log (sparseScalarF s a) +
        θ * Real.log (sparseScalarF s b) +
          (1 / 2 : ℝ) *
            (Real.log p - (1 - θ) * Real.log a - θ * Real.log b) := by
  have hFa : 0 < sparseScalarF s a := sparseScalarF_pos hs ha
  have hFb : 0 < sparseScalarF s b := sparseScalarF_pos hs hb
  have hden : 0 < a ^ (1 - θ) * b ^ θ :=
    mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have hroot : 0 < Real.sqrt (p / (a ^ (1 - θ) * b ^ θ)) :=
    Real.sqrt_pos.2 (div_pos hp0 hden)
  rw [Real.log_mul
      (mul_ne_zero (Real.rpow_pos_of_pos hFa _).ne'
        (Real.rpow_pos_of_pos hFb _).ne') hroot.ne',
    Real.log_mul (Real.rpow_pos_of_pos hFa _).ne'
      (Real.rpow_pos_of_pos hFb _).ne',
    Real.log_rpow hFa, Real.log_rpow hFb,
    Real.log_sqrt (div_nonneg hp0.le hden.le),
    Real.log_div hp0.ne' hden.ne',
    Real.log_mul (Real.rpow_pos_of_pos ha _).ne'
      (Real.rpow_pos_of_pos hb _).ne',
    Real.log_rpow ha, Real.log_rpow hb]
  ring

/-- The equivalent multiplicative `F_s` form of L5.  The logarithmic
statement is the paper-facing consumer; this producer keeps the exact square
root correction visible to later certificate code. -/
theorem sparseScalarF_mul_rpow_sqrt_le {s a b p θ : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hp0 : 0 < p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : p = (1 - θ) * a + θ * b) :
    sparseScalarF s p ≤
      sparseScalarF s a ^ (1 - θ) * sparseScalarF s b ^ θ *
        Real.sqrt (p / (a ^ (1 - θ) * b ^ θ)) := by
  have hFp : 0 < sparseScalarF s p := sparseScalarF_pos hs hp0
  have hFa : 0 < sparseScalarF s a := sparseScalarF_pos hs ha
  have hFb : 0 < sparseScalarF s b := sparseScalarF_pos hs hb
  have hden : 0 < a ^ (1 - θ) * b ^ θ :=
    mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have hR : 0 < sparseScalarF s a ^ (1 - θ) * sparseScalarF s b ^ θ *
      Real.sqrt (p / (a ^ (1 - θ) * b ^ θ)) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hFa _)
      (Real.rpow_pos_of_pos hFb _))
      (Real.sqrt_pos.2 (div_pos hp0 hden))
  apply (Real.log_le_log_iff hFp hR).mp
  calc
    Real.log (sparseScalarF s p) ≤
        (1 - θ) * Real.log (sparseScalarF s a) +
          θ * Real.log (sparseScalarF s b) +
            (1 / 2 : ℝ) *
              (Real.log p - (1 - θ) * Real.log a - θ * Real.log b) :=
      sparseScalarF_log_interpolation hs ha hb hab hp0 hθ0 hθ1 hp
    _ = Real.log
        (sparseScalarF s a ^ (1 - θ) * sparseScalarF s b ^ θ *
          Real.sqrt (p / (a ^ (1 - θ) * b ^ θ))) := by
      symm
      exact sparseScalarF_log_rhs hs ha hb hp0

/-- The paper-shaped interval form of L5.  The interpolation parameter is
defined from the interval endpoints, rather than being supplied as a second
independent premise.  Its proof consumes the multiplicative `F_s` producer,
so the two public forms share one normalization boundary. -/
theorem sparseScalarF_log_interpolation_on_interval {s a b p : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hab : a < b)
    (hpa : a ≤ p) (hpb : p ≤ b) :
    Real.log (sparseScalarF s p) ≤
      (1 - (p - a) / (b - a)) * Real.log (sparseScalarF s a) +
        ((p - a) / (b - a)) * Real.log (sparseScalarF s b) +
          (1 / 2 : ℝ) *
            (Real.log p -
              (1 - (p - a) / (b - a)) * Real.log a -
              ((p - a) / (b - a)) * Real.log b) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hθ0 : 0 ≤ (p - a) / (b - a) :=
    div_nonneg (sub_nonneg.mpr hpa) hba.le
  have hθ1 : (p - a) / (b - a) ≤ 1 := by
    apply (div_le_iff₀ hba).2
    linarith
  have hp0 : 0 < p := lt_of_lt_of_le ha hpa
  have hp : p = (1 - (p - a) / (b - a)) * a +
      ((p - a) / (b - a)) * b := by
    field_simp [ne_of_gt hba]
    ring
  have hmul := sparseScalarF_mul_rpow_sqrt_le
    hs ha (lt_trans ha hab) hab hp0 hθ0 hθ1 hp
  have hFp : 0 < sparseScalarF s p := sparseScalarF_pos hs hp0
  have hFa : 0 < sparseScalarF s a := sparseScalarF_pos hs ha
  have hFb : 0 < sparseScalarF s b :=
    sparseScalarF_pos hs (lt_trans ha hab)
  have hden : 0 < a ^ (1 - (p - a) / (b - a)) *
      b ^ ((p - a) / (b - a)) :=
    mul_pos
      (Real.rpow_pos_of_pos ha _)
      (Real.rpow_pos_of_pos (lt_trans ha hab) _)
  have hR : 0 <
      sparseScalarF s a ^ (1 - (p - a) / (b - a)) *
        sparseScalarF s b ^ ((p - a) / (b - a)) *
          Real.sqrt (p /
            (a ^ (1 - (p - a) / (b - a)) *
              b ^ ((p - a) / (b - a)))) := by
    exact mul_pos
      (mul_pos
        (Real.rpow_pos_of_pos hFa _)
        (Real.rpow_pos_of_pos hFb _))
      (Real.sqrt_pos.2 (div_pos hp0 hden))
  have hlog : Real.log (sparseScalarF s p) ≤
      Real.log
        (sparseScalarF s a ^ (1 - (p - a) / (b - a)) *
          sparseScalarF s b ^ ((p - a) / (b - a)) *
            Real.sqrt (p /
              (a ^ (1 - (p - a) / (b - a)) *
                b ^ ((p - a) / (b - a))))) :=
    (Real.log_le_log_iff hFp hR).mpr hmul
  calc
    Real.log (sparseScalarF s p) ≤
        Real.log
          (sparseScalarF s a ^ (1 - (p - a) / (b - a)) *
            sparseScalarF s b ^ ((p - a) / (b - a)) *
              Real.sqrt (p /
                (a ^ (1 - (p - a) / (b - a)) *
                  b ^ ((p - a) / (b - a))))) := hlog
    _ = (1 - (p - a) / (b - a)) *
          Real.log (sparseScalarF s a) +
        ((p - a) / (b - a)) * Real.log (sparseScalarF s b) +
          (1 / 2 : ℝ) *
            (Real.log p -
              (1 - (p - a) / (b - a)) * Real.log a -
              ((p - a) / (b - a)) * Real.log b) := by
      exact sparseScalarF_log_rhs hs ha (lt_trans ha hab) hp0

end CertifiedProjections
