/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Projection.L2.Lower.SparseRademacher.Shared.Scalar.Interpolation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Half-open Gaussian lobes for the scalar L6 bound

The scalar L6 argument is indexed by all `k : ℤ`.  The lobe sets below are
half-open, so they are genuinely pairwise disjoint; this avoids the endpoint
overlap hidden by a notation using closed intervals.  The local cosine bound
is proved analytically and the translated version uses the antiperiodicity of
cosine, not sampled endpoint data.

The paper's displayed intervals in `euclidean_lower_tails.tex:178--191` are
closed.  Replacing each by `Ico` changes only the countable set of shared
endpoints, preserves the union, and gives the disjoint measurable partition
needed by `integral_iUnion`; this is the formal measure-theoretic convention
used by the theorems below.
-/

open scoped BigOperators NNReal

open MeasureTheory Set

namespace CertifiedProjections

/-- The half-open `k`th cosine lobe. -/
def scalarLobe (k : ℤ) : Set ℝ :=
  Set.Ico (((k : ℝ) - 1 / 2) * Real.pi) (((k : ℝ) + 1 / 2) * Real.pi)

/-- The closed lobe displayed in the paper's periodization argument.  The
half-open `scalarLobe` is the formal partition used for Tonelli. -/
def scalarLobeClosed (k : ℤ) : Set ℝ :=
  Set.Icc (((k : ℝ) - 1 / 2) * Real.pi) (((k : ℝ) + 1 / 2) * Real.pi)

/-- The paper's closed lobe and the formal half-open lobe differ only at
their shared endpoint, hence are equal almost everywhere for volume. -/
theorem scalarLobeClosed_ae_eq_scalarLobe (k : ℤ) :
    scalarLobeClosed k =ᵐ[volume] scalarLobe k := by
  change Set.Icc _ _ =ᵐ[volume] Set.Ico _ _
  exact (Ico_ae_eq_Icc (μ := volume)).symm

/-- Set integrals over the paper's closed lobe and the formal half-open lobe
are identical.  This is the named endpoint convention consumed by the L6
partition rather than an implicit appeal to “up to endpoints”. -/
theorem scalarLobeClosed_setIntegral_eq_scalarLobe_setIntegral
    (f : ℝ → ℝ) (k : ℤ) :
    (∫ y in scalarLobeClosed k, f y) = ∫ y in scalarLobe k, f y := by
  change (∫ y in Set.Icc _ _, f y) = ∫ y in Set.Ico _ _, f y
  exact integral_Icc_eq_integral_Ico

theorem measurableSet_scalarLobe (k : ℤ) : MeasurableSet (scalarLobe k) := by
  exact measurableSet_Ico

theorem scalarLobe_mem_iff {k : ℤ} {y : ℝ} : y ∈ scalarLobe k ↔
    (((k : ℝ) - 1 / 2) * Real.pi ≤ y ∧
      y < ((k : ℝ) + 1 / 2) * Real.pi) := by
  rfl

theorem scalarLobe_pairwise_disjoint :
    Pairwise (fun k l => Disjoint (scalarLobe k) (scalarLobe l)) := by
  intro k l hkl
  have hdis : ∀ {k l : ℤ}, k < l →
      Disjoint (scalarLobe k) (scalarLobe l) := by
    intro k l hkl'
    rw [Set.disjoint_left]
    intro y hyk hyl
    rcases hyk with ⟨_, hyk₁⟩
    rcases hyl with ⟨hyl₀, _⟩
    have hcast : (k : ℝ) + 1 ≤ (l : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hkl')
    have hbridge : ((k : ℝ) + 1 / 2) * Real.pi ≤
        ((l : ℝ) - 1 / 2) * Real.pi := by
      gcongr
      linarith
    linarith
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hdis h
  · exact (hdis h).symm

theorem scalarLobe_cover : (⋃ k : ℤ, scalarLobe k) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  let k : ℤ := ⌊y / Real.pi + 1 / 2⌋
  have hk₀ : (k : ℝ) ≤ y / Real.pi + 1 / 2 := by
    exact_mod_cast (Int.floor_le (y / Real.pi + 1 / 2))
  have hk₁ : y / Real.pi + 1 / 2 < (k : ℝ) + 1 := by
    exact_mod_cast (Int.lt_floor_add_one (y / Real.pi + 1 / 2))
  have hpi : 0 < Real.pi := Real.pi_pos
  have hleft : (((k : ℝ) - 1 / 2) * Real.pi) ≤ y := by
    apply (le_div_iff₀ hpi).mp
    nlinarith
  have hright : y < (((k : ℝ) + 1 / 2) * Real.pi) := by
    apply (div_lt_iff₀ hpi).mp
    nlinarith
  exact Set.mem_iUnion.2 ⟨k, hleft, hright⟩

private lemma scalarCosineEnvelope_core {x : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ Real.pi / 2) :
    Real.cos x ≤ Real.exp (-x ^ 2 / 2) := by
  let f : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2) * Real.cos t
  have hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)) := by
    fun_prop
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc 0 (Real.pi / 2))) := by
    fun_prop
  have hderiv : ∀ t ∈ interior (Set.Icc 0 (Real.pi / 2)),
      deriv f t ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have htpos : 0 < t := ht.1
    have htlt : t < Real.pi / 2 := ht.2
    have hcos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htlt⟩
    have htan : t ≤ Real.tan t := Real.le_tan htpos.le htlt
    have htan' : t * Real.cos t ≤ Real.sin t := by
      rw [Real.tan_eq_sin_div_cos] at htan
      exact (le_div_iff₀ hcos).mp htan
    have hcomp := (Real.hasDerivAt_exp (t ^ 2 / 2)).comp t
      ((hasDerivAt_pow 2 t).div_const 2)
    have hprod := hcomp.mul (Real.hasDerivAt_cos t)
    have hderiv' : deriv f t =
        Real.exp (t ^ 2 / 2) * (t * Real.cos t - Real.sin t) := by
      change deriv ((Real.exp ∘ fun x : ℝ => x ^ 2 / 2) * Real.cos) t = _
      rw [hprod.deriv]
      simp only [Function.comp_apply]
      norm_num
      ring
    rw [hderiv']
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr htan')
  have hanti : AntitoneOn f (Set.Icc 0 (Real.pi / 2)) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 (Real.pi / 2)) hcont hdiff hderiv
  have hmono := hanti (left_mem_Icc.mpr (by positivity : (0 : ℝ) ≤ Real.pi / 2))
      ⟨hx₀, hx₁⟩ hx₀
  have hfzero : f 0 = 1 := by simp [f]
  have hprod : Real.exp (x ^ 2 / 2) * Real.cos x ≤ 1 := by
    simpa [hfzero] using hmono
  calc
    Real.cos x = Real.exp (-x ^ 2 / 2) *
        (Real.exp (x ^ 2 / 2) * Real.cos x) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ ≤ Real.exp (-x ^ 2 / 2) * 1 :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-x ^ 2 / 2) := by ring

theorem scalarCosineEnvelope {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    |Real.cos x| ≤ Real.exp (-x ^ 2 / 2) := by
  rcases le_total 0 x with hx₀ | hx₀
  · have hx' : x ≤ Real.pi / 2 := by simpa [abs_of_nonneg hx₀] using hx
    have h := scalarCosineEnvelope_core hx₀ hx'
    rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hx'⟩)]
    exact h
  · have hx' : -x ≤ Real.pi / 2 := by
      simpa [abs_of_nonpos hx₀] using hx
    have h := scalarCosineEnvelope_core (x := -x) (by linarith) hx'
    have hcos : 0 ≤ Real.cos (-x) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hx'⟩
    calc
      |Real.cos x| = |Real.cos (-x)| := by rw [Real.cos_neg]
      _ = Real.cos (-x) := abs_of_nonneg hcos
      _ ≤ Real.exp (-(-x) ^ 2 / 2) := h
      _ = Real.exp (-x ^ 2 / 2) := by congr 2; ring

theorem scalarLobe_cosineEnvelope {k : ℤ} {y : ℝ} (hy : y ∈ scalarLobe k) :
    |Real.cos y| ≤ Real.exp (-((y - (k : ℝ) * Real.pi) ^ 2) / 2) := by
  have hy₀ := hy.1
  have hy₁ := hy.2
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx : |y - (k : ℝ) * Real.pi| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hcos : |Real.cos y| = |Real.cos (y - (k : ℝ) * Real.pi)| := by
    rw [Real.cos_sub_int_mul_pi]
    simp only [abs_mul]
    norm_num [Int.cast_negOnePow]
  rw [hcos]
  exact scalarCosineEnvelope hx

/-- The Gaussian product which bounds the integrand on the `k`th lobe. -/
noncomputable def scalarLobeGaussian (s p : ℝ) (k : ℤ) (y : ℝ) : ℝ :=
  Real.exp (-(p / (2 * s)) * y ^ 2) *
    Real.exp (-(p / 2) * (y - (k : ℝ) * Real.pi) ^ 2)

theorem scalarLobeIntegrand_le_gaussian_lobe {s p : ℝ} {k : ℤ} {y : ℝ}
    (_hs : 0 < s) (hp : 0 < p) (hy : y ∈ scalarLobe k) :
    scalarLobeIntegrand s p y ≤ scalarLobeGaussian s p k y := by
  have hcos := scalarLobe_cosineEnvelope hy
  have hbase :
      0 ≤ Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y| :=
    mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hbound :
      Real.exp (-y ^ 2 / (2 * s)) * |Real.cos y| ≤
        Real.exp (-y ^ 2 / (2 * s)) *
          Real.exp (-((y - (k : ℝ) * Real.pi) ^ 2) / 2) := by
    exact mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
  have hpow := Real.rpow_le_rpow hbase hbound hp.le
  unfold scalarLobeIntegrand at hpow ⊢
  have hright :
      Real.rpow (Real.exp (-y ^ 2 / (2 * s)) *
        Real.exp (-((y - (k : ℝ) * Real.pi) ^ 2) / 2)) p =
        scalarLobeGaussian s p k y := by
    unfold scalarLobeGaussian
    change (Real.exp (-y ^ 2 / (2 * s)) *
      Real.exp (-((y - (k : ℝ) * Real.pi) ^ 2) / 2)) ^ p = _
    rw [Real.mul_rpow (Real.exp_pos _).le (Real.exp_pos _).le]
    rw [← Real.exp_mul, ← Real.exp_mul]
    congr 1 <;> ring
  exact hpow.trans_eq hright

/-- The exact completed-square identity used before integrating a lobe. -/
theorem scalarLobeGaussian_completedSquare {s p : ℝ} (hs : 0 < s) (hp : 0 < p)
    (k : ℤ) (y : ℝ) :
    scalarLobeGaussian s p k y =
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) *
        Real.exp (-(p * (1 + s) / (2 * s)) *
          (y - s * ((k : ℝ) * Real.pi) / (1 + s)) ^ 2) := by
  unfold scalarLobeGaussian
  have hs1 : 1 + s ≠ 0 := by linarith
  calc
    Real.exp (-(p / (2 * s)) * y ^ 2) *
        Real.exp (-(p / 2) * (y - (k : ℝ) * Real.pi) ^ 2) =
      Real.exp (-(p / (2 * s)) * y ^ 2 +
        (-(p / 2) * (y - (k : ℝ) * Real.pi) ^ 2)) := by
          rw [Real.exp_add]
    _ = Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)) +
        (-(p * (1 + s) / (2 * s)) *
          (y - s * ((k : ℝ) * Real.pi) / (1 + s)) ^ 2)) := by
          congr 1
          field_simp [hs.ne', hs1]
          ring
    _ = Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) *
        Real.exp (-(p * (1 + s) / (2 * s)) *
          (y - s * ((k : ℝ) * Real.pi) / (1 + s)) ^ 2) := by
          rw [Real.exp_add]

private lemma scalarLobeGaussian_integrable {s p : ℝ} (hs : 0 < s) (hp : 0 < p)
    (k : ℤ) : Integrable (scalarLobeGaussian s p k) := by
  rw [show scalarLobeGaussian s p k = fun y =>
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) *
        Real.exp (-(p * (1 + s) / (2 * s)) *
          (y - s * ((k : ℝ) * Real.pi) / (1 + s)) ^ 2) by
    funext y
    exact scalarLobeGaussian_completedSquare hs hp k y]
  apply Integrable.const_mul
  exact (integrable_exp_neg_mul_sq (b := p * (1 + s) / (2 * s)) (by positivity)).comp_sub_right _

/-- The unrestricted Gaussian integral for a single completed lobe. -/
theorem scalarLobeGaussian_integral {s p : ℝ} (hs : 0 < s) (hp : 0 < p)
    (k : ℤ) :
    ∫ y : ℝ, scalarLobeGaussian s p k y =
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) *
        Real.sqrt (2 * Real.pi * s / (p * (1 + s))) := by
  rw [show scalarLobeGaussian s p k = fun y =>
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) *
        Real.exp (-(p * (1 + s) / (2 * s)) *
          (y - s * ((k : ℝ) * Real.pi) / (1 + s)) ^ 2) by
    funext y
    exact scalarLobeGaussian_completedSquare hs hp k y]
  rw [integral_const_mul,
    integral_sub_right_eq_self
      (f := fun x : ℝ => Real.exp (-(p * (1 + s) / (2 * s)) * x ^ 2))
      (s * ((k : ℝ) * Real.pi) / (1 + s)), integral_gaussian]
  congr 2
  have hs1 : 1 + s ≠ 0 := by linarith
  field_simp [hs.ne', hp.ne', hs1]

theorem scalarLobeIntegrand_setIntegral_le_gaussian {s p : ℝ} (hs : 0 < s)
    (hp : 0 < p) (k : ℤ) :
    (∫ y in scalarLobe k, scalarLobeIntegrand s p y) ≤
      ∫ y in scalarLobe k, scalarLobeGaussian s p k y := by
  apply setIntegral_mono_on
    (scalarLobeIntegrand_integrable hs hp).integrableOn
    (scalarLobeGaussian_integrable hs hp k).integrableOn
    (measurableSet_scalarLobe k)
  intro y hy
  exact scalarLobeIntegrand_le_gaussian_lobe hs hp hy

theorem scalarLobeGaussian_setIntegral_le_integral {s p : ℝ} (hs : 0 < s)
    (hp : 0 < p) (k : ℤ) :
    (∫ y in scalarLobe k, scalarLobeGaussian s p k y) ≤
      ∫ y : ℝ, scalarLobeGaussian s p k y := by
  apply setIntegral_le_integral (scalarLobeGaussian_integrable hs hp k)
  filter_upwards [] with y
  exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem scalarLobeIntegral_eq_tsum_setIntegrals {s p : ℝ} (hs : 0 < s)
    (hp : 0 < p) :
    scalarLobeIntegral s p =
      ∑' k : ℤ, ∫ y in scalarLobe k, scalarLobeIntegrand s p y := by
  unfold scalarLobeIntegral
  have h := integral_iUnion (f := scalarLobeIntegrand s p)
    (fun k : ℤ => measurableSet_scalarLobe k)
    scalarLobe_pairwise_disjoint
    ((scalarLobeIntegrand_integrable hs hp).integrableOn.mono_set
      (by rw [scalarLobe_cover]))
  rw [scalarLobe_cover] at h
  simpa using h

private lemma summable_int_exp_neg_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℤ => Real.exp (-a * (k : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply Real.summable_exp_nat_mul_of_ge (c := -a) (by linarith)
    intro n
    cases n with
    | zero => simp
    | succ n =>
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith [sq_nonneg (n : ℝ)]
  · apply Real.summable_exp_nat_mul_of_ge (c := -a) (by linarith)
    intro n
    cases n with
    | zero => simp
    | succ n =>
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith [sq_nonneg (n : ℝ)]

/-- Both first nonzero integer lobes occur in the full Gaussian sum. -/
theorem scalarLobe_integer_two_sided_nonzero {a : ℝ} (ha : 0 < a) :
    2 * Real.exp (-a) ≤
      ∑' k : ℤ, Real.exp (-a * (k : ℝ) ^ 2) := by
  have hsum := (summable_int_exp_neg_sq ha).sum_le_tsum
    ({(-1 : ℤ), 1} : Finset ℤ)
    (by
      intro k _
      positivity)
  have hsum' : Real.exp (-a) + Real.exp (-a) ≤
      ∑' k : ℤ, Real.exp (-a * (k : ℝ) ^ 2) := by
    simpa using hsum
  calc
    2 * Real.exp (-a) = Real.exp (-a) + Real.exp (-a) := by ring
    _ ≤ ∑' k : ℤ, Real.exp (-a * (k : ℝ) ^ 2) := hsum'

private lemma scalarLobeGaussian_integrals_summable {s p : ℝ} (hs : 0 < s)
    (hp : 0 < p) :
    Summable (fun k : ℤ => ∫ y : ℝ, scalarLobeGaussian s p k y) := by
  let a : ℝ := p * Real.pi ^ 2 / (2 * (1 + s))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hsum := (summable_int_exp_neg_sq ha).mul_right
    (Real.sqrt (2 * Real.pi * s / (p * (1 + s))))
  refine hsum.congr ?_
  intro k
  rw [scalarLobeGaussian_integral hs hp]
  congr 1
  dsimp [a]
  ring

theorem scalarLobeIntegral_le_tsum_gaussian_integrals {s p : ℝ} (hs : 0 < s)
    (hp : 0 < p) :
    scalarLobeIntegral s p ≤
      ∑' k : ℤ, ∫ y : ℝ, scalarLobeGaussian s p k y := by
  rw [scalarLobeIntegral_eq_tsum_setIntegrals hs hp]
  have hsum_lobes := (hasSum_integral_iUnion
    (f := scalarLobeIntegrand s p)
    (fun k : ℤ => measurableSet_scalarLobe k)
    scalarLobe_pairwise_disjoint
    ((scalarLobeIntegrand_integrable hs hp).integrableOn.mono_set
      (by rw [scalarLobe_cover]))).summable
  exact hsum_lobes.tsum_le_tsum
      (fun k => (scalarLobeIntegrand_setIntegral_le_gaussian hs hp k).trans
        (scalarLobeGaussian_setIntegral_le_integral hs hp k))
      (scalarLobeGaussian_integrals_summable hs hp)

private lemma scalarLobe_normalization {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    Real.sqrt (p / (2 * Real.pi * s)) *
        Real.sqrt (2 * Real.pi * s / (p * (1 + s))) =
      1 / Real.sqrt (1 + s) := by
  have hleft : 0 ≤ Real.sqrt (p / (2 * Real.pi * s)) *
      Real.sqrt (2 * Real.pi * s / (p * (1 + s))) := by positivity
  have hright : 0 ≤ 1 / Real.sqrt (1 + s) := by positivity
  have hleft_sq :
      (Real.sqrt (p / (2 * Real.pi * s)) *
        Real.sqrt (2 * Real.pi * s / (p * (1 + s)))) ^ 2 =
        1 / (1 + s) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp [hs.ne', hp.ne', (show 1 + s ≠ 0 by linarith)]
  have hright_sq : (1 / Real.sqrt (1 + s)) ^ 2 = 1 / (1 + s) := by
    rw [div_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + s)]
    norm_num
  nlinarith

private lemma scalarLobeGaussian_tsum_eq {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    (∑' k : ℤ, ∫ y : ℝ, scalarLobeGaussian s p k y) =
      (∑' k : ℤ,
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) *
        Real.sqrt (2 * Real.pi * s / (p * (1 + s))) := by
  calc
    (∑' k : ℤ, ∫ y : ℝ, scalarLobeGaussian s p k y) =
        ∑' k : ℤ,
          Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) *
            Real.sqrt (2 * Real.pi * s / (p * (1 + s))) := by
      congr 1
      funext k
      exact scalarLobeGaussian_integral hs hp k
    _ = (∑' k : ℤ,
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) *
          Real.sqrt (2 * Real.pi * s / (p * (1 + s))) := by
      let a : ℝ := p * Real.pi ^ 2 / (2 * (1 + s))
      have hterm : (fun k : ℤ =>
          Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) =
          (fun k : ℤ => Real.exp (-a * (k : ℝ) ^ 2)) := by
        funext k
        congr 1
        dsimp [a]
        ring
      have hsumterm :
          (∑' k : ℤ,
            Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) =
            ∑' k : ℤ, Real.exp (-a * (k : ℝ) ^ 2) := by
        apply tsum_congr
        intro k
        exact congrFun hterm k
      calc
        (∑' k : ℤ,
            Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) *
              Real.sqrt (2 * Real.pi * s / (p * (1 + s)))) =
            ∑' k : ℤ, Real.exp (-a * (k : ℝ) ^ 2) *
              Real.sqrt (2 * Real.pi * s / (p * (1 + s))) := by
          apply tsum_congr
          intro k
          exact congrArg (fun z : ℝ => z *
            Real.sqrt (2 * Real.pi * s / (p * (1 + s)))) (congrFun hterm k)
        _ = (∑' k : ℤ, Real.exp (-a * (k : ℝ) ^ 2)) *
              Real.sqrt (2 * Real.pi * s / (p * (1 + s))) :=
          (summable_int_exp_neg_sq (a := a) (by positivity)).tsum_mul_right _
        _ = (∑' k : ℤ,
            Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) *
              Real.sqrt (2 * Real.pi * s / (p * (1 + s))) := by
          rw [hsumterm]

/-- The full integer-lobe Gaussian upper bound (paper L6).

The sum is deliberately left as a sum over all `k : ℤ`; later tail
producers may split its zero and nonzero terms, but this theorem does not
silently discard either side of the periodization.
-/
theorem sparseScalarF_lobe_periodization {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    sparseScalarF s p ≤
      1 / Real.sqrt (1 + s) *
        ∑' k : ℤ,
          Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) := by
  let A : ℝ := Real.sqrt (p / (2 * Real.pi * s))
  have hI := scalarLobeIntegral_le_tsum_gaussian_integrals hs hp
  have hA : 0 ≤ A := by positivity
  calc
    sparseScalarF s p = A * scalarLobeIntegral s p := by
      simpa [A] using sparseScalarF_eq_sqrt_mul_scalarLobeIntegral hs hp
    _ ≤ A * (∑' k : ℤ, ∫ y : ℝ, scalarLobeGaussian s p k y) :=
      mul_le_mul_of_nonneg_left hI hA
    _ = A * ((∑' k : ℤ,
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) *
          Real.sqrt (2 * Real.pi * s / (p * (1 + s)))) := by
      rw [scalarLobeGaussian_tsum_eq hs hp]
    _ = (A * Real.sqrt (2 * Real.pi * s / (p * (1 + s)))) *
        (∑' k : ℤ,
          Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) := by
      ring
    _ = 1 / Real.sqrt (1 + s) *
        ∑' k : ℤ,
          Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) := by
      rw [show A = Real.sqrt (p / (2 * Real.pi * s)) by rfl,
        scalarLobe_normalization hs hp]

/-- After removing the central cosine lobe, only the nonzero Gaussian images
remain in the periodization bound.  This is the form needed when another
factor is retained and estimated sharply on the central lobe. -/
theorem scalarLobeIntegral_compl_zero_le_tsum_gaussian_nonzero
    {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    (∫ y in (scalarLobe 0)ᶜ, scalarLobeIntegrand s p y) ≤
      ∑' k : {k : ℤ // k ≠ 0},
        ∫ y : ℝ, scalarLobeGaussian s p k y := by
  let I : Type := {k : ℤ // k ≠ 0}
  have hcover : (⋃ k : I, scalarLobe (k : ℤ)) = (scalarLobe 0)ᶜ := by
    ext y
    constructor
    · intro hy
      obtain ⟨k, hyk⟩ := Set.mem_iUnion.1 hy
      intro hy0
      have hne : (k : ℤ) ≠ 0 := k.property
      exact (Set.disjoint_left.1 (scalarLobe_pairwise_disjoint hne) hyk hy0)
    · intro hy
      have hall : y ∈ ⋃ k : ℤ, scalarLobe k := by
        rw [scalarLobe_cover]
        exact Set.mem_univ y
      obtain ⟨k, hyk⟩ := Set.mem_iUnion.1 hall
      have hk : k ≠ 0 := by
        intro hzero
        subst k
        exact hy hyk
      exact Set.mem_iUnion.2 ⟨⟨k, hk⟩, hyk⟩
  have hdis : Pairwise (fun k l : I =>
      Disjoint (scalarLobe (k : ℤ)) (scalarLobe (l : ℤ))) := by
    intro k l hkl
    exact scalarLobe_pairwise_disjoint (fun hval => hkl (Subtype.ext hval))
  have hdecomp := integral_iUnion
    (f := scalarLobeIntegrand s p)
    (fun k : I => measurableSet_scalarLobe (k : ℤ)) hdis
    ((scalarLobeIntegrand_integrable hs hp).integrableOn.mono_set
      (by rw [hcover]))
  rw [hcover] at hdecomp
  rw [hdecomp]
  have hsum_lobes := (hasSum_integral_iUnion
    (f := scalarLobeIntegrand s p)
    (fun k : I => measurableSet_scalarLobe (k : ℤ)) hdis
    ((scalarLobeIntegrand_integrable hs hp).integrableOn.mono_set
      (by rw [hcover]))).summable
  exact hsum_lobes.tsum_le_tsum
    (fun k =>
      (scalarLobeIntegrand_setIntegral_le_gaussian hs hp (k : ℤ)).trans
        (scalarLobeGaussian_setIntegral_le_integral hs hp (k : ℤ)))
    ((scalarLobeGaussian_integrals_summable hs hp).subtype _)

/-- The Gaussian scalar moment restricted away from its central cosine lobe
is the normalized complement of the unnormalised lobe integral. -/
theorem sparseScalarF_compl_centralLobe_eq
    {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    (∫ G in {G : ℝ | Real.sqrt (s / p) * G ∈ scalarLobe 0}ᶜ,
        sparseScalarFIntegrand s p G ∂(ProbabilityTheory.gaussianReal 0 1)) =
      Real.sqrt (p / (2 * Real.pi * s)) *
        ∫ y in (scalarLobe 0)ᶜ, scalarLobeIntegrand s p y := by
  let a : ℝ := Real.sqrt (s / p)
  let C : Set ℝ := {G : ℝ | a * G ∈ scalarLobe 0}
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hC : MeasurableSet C :=
    (measurableSet_scalarLobe 0).preimage (by fun_prop)
  have hpoint (G : ℝ) :
      ProbabilityTheory.gaussianPDFReal 0 1 G *
          Cᶜ.indicator (sparseScalarFIntegrand s p) G =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          (scalarLobe 0)ᶜ.indicator (scalarLobeIntegrand s p) (a * G) := by
    by_cases hmem : G ∈ Cᶜ
    · have himage : a * G ∈ (scalarLobe 0)ᶜ := hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem himage]
      rw [ProbabilityTheory.gaussianPDFReal]
      simp only [NNReal.coe_one, sub_zero, mul_one]
      rw [show a = Real.sqrt (s / p) by rfl,
        scalarLobeIntegrand_scale_eq hs hp]
      ring
    · have hnotImage : a * G ∉ (scalarLobe 0)ᶜ := by
        simpa [C] using hmem
      rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem hnotImage]
      ring
  have hfactor :
      (Real.sqrt (2 * Real.pi))⁻¹ * a⁻¹ =
        Real.sqrt (p / (2 * Real.pi * s)) := by
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    have hsp : 0 ≤ s / p := (div_pos hs hp).le
    have hleft : 0 ≤
        (Real.sqrt (2 * Real.pi))⁻¹ * a⁻¹ := by positivity
    have hright : 0 ≤ Real.sqrt (p / (2 * Real.pi * s)) :=
      Real.sqrt_nonneg _
    have hleft_sq :
        ((Real.sqrt (2 * Real.pi))⁻¹ * a⁻¹) ^ 2 =
          p / (2 * Real.pi * s) := by
      dsimp [a]
      rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt hpi,
        Real.sq_sqrt hsp]
      field_simp
    have hright_sq :
        (Real.sqrt (p / (2 * Real.pi * s))) ^ 2 =
          p / (2 * Real.pi * s) := by
      exact Real.sq_sqrt (by positivity)
    nlinarith
  rw [show {G : ℝ | Real.sqrt (s / p) * G ∈ scalarLobe 0} = C by rfl]
  rw [← integral_indicator hC.compl]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  calc
    (∫ G : ℝ, ProbabilityTheory.gaussianPDFReal 0 1 G *
        Cᶜ.indicator (sparseScalarFIntegrand s p) G) =
      ∫ G : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ *
        (scalarLobe 0)ᶜ.indicator (scalarLobeIntegrand s p) (a * G) := by
          apply integral_congr_ae
          filter_upwards [] with G
          exact hpoint G
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ G : ℝ,
          (scalarLobe 0)ᶜ.indicator (scalarLobeIntegrand s p) (a * G) := by
      rw [integral_const_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        (a⁻¹ * ∫ y : ℝ,
          (scalarLobe 0)ᶜ.indicator (scalarLobeIntegrand s p) y) := by
      rw [Measure.integral_comp_mul_left]
      rw [abs_of_pos (inv_pos.mpr ha)]
      rfl
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * a⁻¹ *
        (∫ y in (scalarLobe 0)ᶜ, scalarLobeIntegrand s p y) := by
      rw [integral_indicator (measurableSet_scalarLobe 0).compl]
      ring
    _ = Real.sqrt (p / (2 * Real.pi * s)) *
        ∫ y in (scalarLobe 0)ᶜ, scalarLobeIntegrand s p y := by
      rw [hfactor]

/-- The noncentral part of the Gaussian scalar moment is bounded by the
nonzero lobe images, with the exact change-of-variables normalization. -/
theorem sparseScalarF_compl_centralLobe_le_tsum_gaussian_nonzero
    {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    (∫ G in {G : ℝ | Real.sqrt (s / p) * G ∈ scalarLobe 0}ᶜ,
        sparseScalarFIntegrand s p G ∂(ProbabilityTheory.gaussianReal 0 1)) ≤
      Real.sqrt (p / (2 * Real.pi * s)) *
        ∑' k : {k : ℤ // k ≠ 0},
          ∫ y : ℝ, scalarLobeGaussian s p k y := by
  rw [sparseScalarF_compl_centralLobe_eq hs hp]
  exact mul_le_mul_of_nonneg_left
    (scalarLobeIntegral_compl_zero_le_tsum_gaussian_nonzero hs hp)
    (Real.sqrt_nonneg _)

/-- Closed nonzero-image form of the complement-of-central-lobe bound. -/
theorem sparseScalarF_compl_centralLobe_le_nonzero_images
    {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    (∫ G in {G : ℝ | Real.sqrt (s / p) * G ∈ scalarLobe 0}ᶜ,
        sparseScalarFIntegrand s p G ∂(ProbabilityTheory.gaussianReal 0 1)) ≤
      1 / Real.sqrt (1 + s) *
        ∑' k : {k : ℤ // k ≠ 0},
          Real.exp (-(p * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
            (2 * (1 + s))) := by
  let A : ℝ := Real.sqrt (p / (2 * Real.pi * s))
  let B : ℝ := Real.sqrt (2 * Real.pi * s / (p * (1 + s)))
  have hbase := sparseScalarF_compl_centralLobe_le_tsum_gaussian_nonzero hs hp
  have hsum : Summable (fun k : {k : ℤ // k ≠ 0} =>
      Real.exp (-(p * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
        (2 * (1 + s)))) := by
    let c : ℝ := p * Real.pi ^ 2 / (2 * (1 + s))
    have hc : 0 < c := by dsimp [c]; positivity
    have h := (summable_int_exp_neg_sq hc).subtype
      {k : ℤ | k ≠ 0}
    have heq : (fun k : {k : ℤ // k ≠ 0} =>
        Real.exp (-(p * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
          (2 * (1 + s)))) =
        (fun k : {k : ℤ // k ≠ 0} =>
          Real.exp (-c * ((k : ℤ) : ℝ) ^ 2)) := by
      funext k
      congr 1
      dsimp [c]
      ring
    rw [heq]
    change Summable ((fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2)) ∘
      Subtype.val)
    exact h
  calc
    (∫ G in {G : ℝ | Real.sqrt (s / p) * G ∈ scalarLobe 0}ᶜ,
        sparseScalarFIntegrand s p G ∂(ProbabilityTheory.gaussianReal 0 1)) ≤
      A * ∑' k : {k : ℤ // k ≠ 0},
        ∫ y : ℝ, scalarLobeGaussian s p k y := by
          simpa only [A] using hbase
    _ = A * ∑' k : {k : ℤ // k ≠ 0},
        Real.exp (-(p * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
          (2 * (1 + s))) * B := by
      congr 1
      apply tsum_congr
      intro k
      rw [scalarLobeGaussian_integral hs hp]
      dsimp [B]
      congr 1
      ring
    _ = A * ((∑' k : {k : ℤ // k ≠ 0},
        Real.exp (-(p * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
          (2 * (1 + s)))) * B) := by
      rw [hsum.tsum_mul_right]
    _ = (A * B) * ∑' k : {k : ℤ // k ≠ 0},
        Real.exp (-(p * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
          (2 * (1 + s))) := by ring
    _ = 1 / Real.sqrt (1 + s) *
        ∑' k : {k : ℤ // k ≠ 0},
          Real.exp (-(p * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
            (2 * (1 + s))) := by
      rw [show A = Real.sqrt (p / (2 * Real.pi * s)) by rfl,
        show B = Real.sqrt (2 * Real.pi * s / (p * (1 + s))) by rfl,
        scalarLobe_normalization hs hp]

end CertifiedProjections
