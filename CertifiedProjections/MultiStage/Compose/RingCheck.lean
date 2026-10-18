/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Compose.Moments
import CertifiedProjections.MultiStage.Lemmas.FalseZero
import CertifiedProjections.Model.Modular.CenteredGeometry

/-!
# Overflow and false zero across stages

`FalseZeroBound K q ε` says that the table kernel `K` produces a false zero with probability at most
`ε`: it maps a table that is nonzero mod `q` to one that is zero mod `q`. This file proves such a
bound for one stage (`FalseZeroBound.stage`), for a deterministic map (`FalseZeroBound.ofFun`) and
for sequential composition (`FalseZeroBound.andThen`).

For a kernel `K` with a moment bound, the output `Y` overflows when centering modulo `p` changes it,
that is, when `ctr p Y ≠ Y`. The theorem `ringCheck_accept_le` bounds the probability that `ctr p Y`
is zero mod `q` when the input is nonzero mod `q`, and `ringCheck_reject_le` bounds the probability
that `ctr p Y` is nonzero mod `q` when the input is zero mod `q` (spec Theorem 5.3 and §7).
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}
variable {f₁ F₁ f₂ F₂ q : ℕ} {ε₁ ε₂ : ℝ≥0∞}
variable {K₁ : TableKernel f F f₁ F₁} {K₂ : TableKernel f₁ F₁ f₂ F₂}

/-- `K` maps a table that is nonzero mod `q` to one that is zero mod `q` with probability at most
`ε`. -/
def FalseZeroBound (K : TableKernel f F f' F') (q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ X, ¬ ZeroMod q X → eventProbability (K X) (ZeroMod q) ≤ ε

/-- If `μ.AtomBound α` holds and `q` is a prime with `2 * μ.bound < q`, a stage with `c` rows
satisfies the false-zero bound with `ε = α ^ c`. -/
theorem FalseZeroBound.stage (μ : EntryLaw) {α : ℝ≥0∞} (hα : μ.AtomBound α) {q : ℕ} (hq : q.Prime)
    (hb : 2 * μ.bound < q) (c : ℕ) :
    FalseZeroBound (MultiStage.stage μ c : TableKernel f F c F) q (α ^ c) := by
  intro X hX
  exact stage_zero_mod_le μ hα hq hb c X hX
/-- A deterministic map `g` for which `g X` is zero mod `q` only if `X` is zero mod `q` satisfies
the false-zero bound with `ε = 0`. -/
theorem FalseZeroBound.ofFun (g : Table f F → Table f' F')
    (hg : ∀ X, ZeroMod q (g X) → ZeroMod q X) :
    FalseZeroBound (TableKernel.ofFun g) q 0 := by
  classical
  intro X hX
  have h : ¬ ZeroMod q (g X) := fun hz => hX (hg X hz)
  simp [TableKernel.ofFun, eventProbability, PMF.pure_map, h]
/-- If `K₁` and `K₂` satisfy the false-zero bound with `ε₁` and `ε₂`, then `K₁.andThen K₂` satisfies
it with `ε₁ + ε₂`. -/
theorem FalseZeroBound.andThen (h₁ : FalseZeroBound K₁ q ε₁) (h₂ : FalseZeroBound K₂ q ε₂) :
    FalseZeroBound (K₁.andThen K₂) q (ε₁ + ε₂) := by
  classical
  intro X hX
  change eventProbability ((K₁ X).bind K₂) (ZeroMod q) ≤ ε₁ + ε₂
  have hbind : eventProbability ((K₁ X).bind K₂) (ZeroMod q) =
      ∑' Y, K₁ X Y * eventProbability (K₂ Y) (ZeroMod q) := by
    simp only [eventProbability, PMF.map_bind, PMF.bind_apply]
  rw [hbind]
  calc
    _ ≤ ∑' Y, K₁ X Y * ((if ZeroMod q Y then 1 else 0) + ε₂) := by
      apply ENNReal.tsum_le_tsum
      intro Y
      apply mul_le_mul' (le_refl _)
      by_cases hY : ZeroMod q Y
      · simpa [hY] using (eventProbability_le_one (K₂ Y) (ZeroMod q)).trans
          (le_self_add : (1 : ℝ≥0∞) ≤ 1 + ε₂)
      · simpa [hY] using h₂ Y hY
    _ = eventProbability (K₁ X) (ZeroMod q) + ε₂ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, (K₁ X).tsum_coe, one_mul,
        eventProbability_eq_tsum]
      congr 1
      apply tsum_congr
      intro Y
      split_ifs <;> simp
    _ ≤ ε₁ + ε₂ := add_le_add (h₁ X hX) (le_refl ε₂)

/-- If centering modulo `p` changes the table `Y`, then `p ^ 2 ≤ 4 * sqNorm Y`. -/
private theorem modulus_sq_le_of_ctr_ne (p : ℕ) (Y : Table f F) (h : ctr p Y ≠ Y) :
    p ^ 2 ≤ 4 * sqNorm Y := by
  classical
  have hex : ∃ k φ, centeredMod p (Y k φ) ≠ Y k φ := by
    by_contra! hfix
    exact h (by ext k φ; exact hfix k φ)
  obtain ⟨k, φ, hentry⟩ := hex
  have hp := centeredMod_modulus_le_natAbs_add_of_ne hentry.symm
  have hc := centeredMod_natAbs_le p (Y k φ)
  have hnorm : (Y k φ).natAbs ^ 2 ≤ sqNorm Y := by
    exact (Finset.single_le_sum (fun i _ => Nat.zero_le ((Y k i).natAbs ^ 2))
      (Finset.mem_univ φ)).trans
      (Finset.single_le_sum (fun i _ => Nat.zero_le (∑ j, (Y i j).natAbs ^ 2))
        (Finset.mem_univ k))
  nlinarith

/-- If `MomentBound K t M` holds and `sqNorm X ≤ H`, the probability that centering modulo `p`
changes the output `Y` of `K X` is at most `M * (4 * H) ^ t / p ^ (2 * t)`. -/
private theorem ctr_ne_probability_le {K : TableKernel f F f' F'} {p t H : ℕ}
    {M : ℝ≥0∞} (hM : MomentBound K t M) (X : Table f F) (hH : sqNorm X ≤ H) :
    eventProbability (K X) (fun Y => ctr p Y ≠ Y) ≤
      M * (4 * H : ℝ≥0∞) ^ t / (p : ℝ≥0∞) ^ (2 * t) := by
  classical
  by_cases hp : p = 0
  · subst p
    rw [eventProbability_eq_tsum]
    simp only [ctr_modulus_zero, ne_eq, not_true_eq_false, ↓reduceIte, tsum_zero]
    exact bot_le
  · have hd₀ : (p : ℝ≥0∞) ^ (2 * t) ≠ 0 := by simp [hp]
    have hd_top : (p : ℝ≥0∞) ^ (2 * t) ≠ ∞ := by finiteness
    calc
      _ ≤ expectation (K X) (fun Y => (4 * sqNorm Y : ℝ≥0∞) ^ t) /
          (p : ℝ≥0∞) ^ (2 * t) := by
        apply eventProbability_le_expectation_div _ _ _ _ hd₀ hd_top
        intro Y _ hY
        have hnat := modulus_sq_le_of_ctr_ne p Y hY
        have hcast : (p : ℝ≥0∞) ^ 2 ≤ 4 * (sqNorm Y : ℝ≥0∞) := by
          exact_mod_cast hnat
        simpa only [pow_mul] using pow_le_pow_left' hcast t
      _ ≤ M * (4 * H : ℝ≥0∞) ^ t / (p : ℝ≥0∞) ^ (2 * t) := by
        apply ENNReal.div_le_div_right
        have hexpect : expectation (K X) (fun Y => (4 * sqNorm Y : ℝ≥0∞) ^ t) =
            (4 : ℝ≥0∞) ^ t * expectation (K X) (fun Y => (sqNorm Y : ℝ≥0∞) ^ t) := by
          simp only [expectation, mul_pow]
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro Y
          ac_rfl
        rw [hexpect, mul_pow]
        calc
          _ ≤ (4 : ℝ≥0∞) ^ t * (M * (H : ℝ≥0∞) ^ t) :=
            mul_le_mul' (le_refl _) ((hM X).trans
              (mul_le_mul' (le_refl M) (pow_le_pow_left' (by exact_mod_cast hH) t)))
          _ = _ := by ac_rfl

/-- Spec Theorem 5.3 for any integer kernel: if `MomentBound K t M` and `FalseZeroBound K q ε` hold,
and the input `X` has `sqNorm X ≤ H` and is nonzero mod `q`, then the probability that the centered
output `ctr p Y` is zero mod `q` is at most `M * (4 * H) ^ t / p ^ (2 * t) + ε`. The first term
bounds the probability of overflow, `ctr p Y ≠ Y`, by Markov's inequality, and `ε` bounds the
probability of a false zero. -/
theorem ringCheck_accept_le {K : TableKernel f F f' F'} {p q t H : ℕ} {M ε : ℝ≥0∞}
    (hM : MomentBound K t M) (hz : FalseZeroBound K q ε) (X : Table f F)
    (hH : sqNorm X ≤ H) (hX : ¬ ZeroMod q X) :
    eventProbability (K X) (fun Y => ZeroMod q (ctr p Y)) ≤
      M * (4 * H : ℝ≥0∞) ^ t / (p : ℝ≥0∞) ^ (2 * t) + ε := by
  classical
  refine (eventProbability_le_add (K X) _ (fun Y => ctr p Y ≠ Y) (ZeroMod q) ?_).trans
    (add_le_add (ctr_ne_probability_le hM X hH) (hz X hX))
  intro Y hY
  by_cases heq : ctr p Y = Y
  · exact Or.inr (heq ▸ hY)
  · exact Or.inl heq
/-- If `MomentBound K t M` holds, `K` maps every table that is zero mod `q` to tables that are zero
mod `q` (hypothesis `hK`), and the input `X` has `sqNorm X ≤ H` and is zero mod `q`, then the
probability that the centered output `ctr p Y` is nonzero mod `q` is at most
`M * (4 * H) ^ t / p ^ (2 * t)`. -/
theorem ringCheck_reject_le {K : TableKernel f F f' F'} {p q t H : ℕ} {M : ℝ≥0∞}
    (hM : MomentBound K t M) (hK : ∀ X, ZeroMod q X → ∀ Y ∈ (K X).support, ZeroMod q Y)
    (X : Table f F) (hH : sqNorm X ≤ H) (hX : ZeroMod q X) :
    eventProbability (K X) (fun Y => ¬ ZeroMod q (ctr p Y)) ≤
      M * (4 * H : ℝ≥0∞) ^ t / (p : ℝ≥0∞) ^ (2 * t) := by
  classical
  refine le_trans ?_ (ctr_ne_probability_le hM X hH)
  rw [eventProbability_eq_tsum, eventProbability_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro Y
  by_cases hY : Y ∈ (K X).support
  · by_cases heq : ctr p Y = Y
    · have hz : ZeroMod q Y := hK X hX Y hY
      simp [hz, heq]
    · simp [heq]
      split_ifs <;> simp
  · have hz : K X Y = 0 := ((K X).apply_eq_zero_iff Y).mpr hY
    simp [hz]

end CertifiedProjections.MultiStage
