/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Branch
import CertifiedProjections.MultiStage.Lemmas.MGF
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.NNRat.Encodable

/-!
# Stochastic domination across stages

A comparison law is a law on `ℚ≥0` that serves as a lower bound for a random quantity. The predicate
`StochGe P V D` says that `V` under `P` is stochastically at least the comparison law `D`: for every
`u`, the probability that `V ≤ u` is at most `cdf D u`, the probability that a draw from `D` is at
most `u`.

This file defines the laws of products and sums of independent draws (`mulLaw`, `addLaw`, `iidProd`,
`iidSum`) and proves that `StochGe` is preserved by sequential products (`StochGe.bind_mul`),
sequential sums (`StochGe.bind_add`), sums of independent draws (`StochGe.piPMF_sum`), and replacing
the quantity by zero on an event of small probability (`StochGe.of_event`). For one stage,
`stage_smallBall_le` bounds the probability that the squared norm shrinks by a factor `u` by
`smallBallBound`, and `stage_stochGe` states the same bound with `StochGe`. The structure
`ComparisonData` collects the comparison laws of a stage, of the final stage and of a whole branch,
and `ComparisonData.failProb` is the probability that the resulting comparison quantity is below a
threshold. This replaces spec Lemma D and is used with Lemma E and Corollary C′.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory

namespace CertifiedProjections.MultiStage

variable {f F f' F' c g : ℕ}
variable {t K : ℝ} {cT L : ℕ} {ε : ℝ≥0∞}

/-- The distribution function of `D`: the probability that a draw from `D` is at most `u`. -/
noncomputable def cdf (D : PMF ℚ≥0) (u : ℚ≥0) : ℝ≥0∞ := eventProbability D (· ≤ u)
/-- The law of the product of independent draws from `D₁` and `D₂`. -/
noncomputable def mulLaw (D₁ D₂ : PMF ℚ≥0) : PMF ℚ≥0 := D₁.bind fun a => D₂.map (a * ·)
/-- The law of the sum of independent draws from `D₁` and `D₂`. -/
noncomputable def addLaw (D₁ D₂ : PMF ℚ≥0) : PMF ℚ≥0 := D₁.bind fun a => D₂.map (a + ·)
/-- The law of the product of `k` independent draws from `D` (`PMF.pure 1` at `k = 0`). -/
noncomputable def iidProd (D : PMF ℚ≥0) : ℕ → PMF ℚ≥0
  | 0 => PMF.pure 1
  | k + 1 => mulLaw D (iidProd D k)
/-- The law of the sum of `k` independent draws from `D` (`PMF.pure 0` at `k = 0`). -/
noncomputable def iidSum (D : PMF ℚ≥0) : ℕ → PMF ℚ≥0
  | 0 => PMF.pure 0
  | k + 1 => addLaw D (iidSum D k)

/-- `V` under `P` is stochastically at least `D`: for every `u`, the probability under `P` that
`V ≤ u` is at most `cdf D u`. -/
def StochGe {α : Type*} (P : PMF α) (V : α → ℚ≥0) (D : PMF ℚ≥0) : Prop :=
  ∀ u, eventProbability P (fun a => V a ≤ u) ≤ cdf D u

/-- Spec (3.12): `F_c(u) = min(1, K^c e^{tu})`. By `stage_smallBall_le`, this bounds the
probability that a stage with `c` rows maps a nonzero table `X` to a table `Y` with
`sqNorm Y ≤ u * sqNorm X`. -/
noncomputable def smallBallBound (t K : ℝ) (c : ℕ) (u : ℚ≥0) : ℝ≥0∞ :=
  min 1 (ENNReal.ofReal (K ^ c * Real.exp (t * (u : ℝ))))
/-- Spec Lemma E: the bound `1 - (1 - ρ ^ c) ^ L` on the probability that some stage of a branch
with `L` stages maps a large table to a small one, when each stage does so with probability at most
`ρ ^ c`. -/
noncomputable def collapseFailBound (ρ : ℝ≥0∞) (c L : ℕ) : ℝ≥0∞ := 1 - (1 - ρ ^ c) ^ L

variable {α : Type*} {P : PMF α} {V : α → ℚ≥0} {D D' : PMF ℚ≥0}

/-- The expectation of `ψ` under a law `P` on `ℚ≥0` is the Lebesgue integral of `ψ` against the
measure of `P`. -/
private theorem expectation_eq_lintegral [MeasurableSpace ℚ≥0] [MeasurableSingletonClass ℚ≥0]
    (P : PMF ℚ≥0) (ψ : ℚ≥0 → ℝ≥0∞) :
    expectation P ψ = ∫⁻ x, ψ x ∂P.toMeasure := by
  rw [MeasureTheory.lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), expectation, mul_comm]

/-- If the measure of `P` is at most the measure of `D` on every interval `Set.Iic u`, then it is at
most the measure of `D` on every lower set `s`. -/
private theorem toMeasure_le_of_isLowerSet [MeasurableSpace ℚ≥0] (P D : PMF ℚ≥0)
    (h : ∀ u, P.toMeasure (Set.Iic u) ≤ D.toMeasure (Set.Iic u))
    (s : Set ℚ≥0) (hs : IsLowerSet s) : P.toMeasure s ≤ D.toMeasure s := by
  classical
  have heq : s = ⋃ q : s, Set.Iic (q : ℚ≥0) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.mpr ⟨(⟨x, hx⟩ : s), ?_⟩
      exact Set.mem_Iic.mpr le_rfl
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
      exact hs hq q.property
  have hd : Directed (· ⊆ ·) (fun q : s => Set.Iic (q : ℚ≥0)) := by
    intro a b
    rcases le_total a.val b.val with hab | hba
    · exact ⟨b, Set.Iic_subset_Iic.mpr hab, Set.Subset.rfl⟩
    · exact ⟨a, Set.Subset.rfl, Set.Iic_subset_Iic.mpr hba⟩
  rw [heq, hd.measure_iUnion, hd.measure_iUnion]
  exact iSup_mono fun q => h q

/-- If the measure of `P` is at most the measure of `D` on every interval `Set.Iic u`, then the
integral of a finite antitone function `ψ` against `P` is at most its integral against `D`. -/
private theorem lintegral_antitone_le [MeasurableSpace ℚ≥0] [MeasurableSingletonClass ℚ≥0]
    (P D : PMF ℚ≥0)
    (h : ∀ u, P.toMeasure (Set.Iic u) ≤ D.toMeasure (Set.Iic u))
    (ψ : ℚ≥0 → ℝ≥0∞) (hψ : Antitone ψ) (hfin : ∀ x, ψ x ≠ ⊤) :
    (∫⁻ x, ψ x ∂P.toMeasure) ≤ ∫⁻ x, ψ x ∂D.toMeasure := by
  have hreal : Antitone (fun x => (ψ x).toReal) := by
    intro x y hxy
    exact ENNReal.toReal_mono (hfin x) (hψ hxy)
  have hrepr : ψ = fun x => ENNReal.ofReal ((ψ x).toReal) := by
    funext x
    exact (ENNReal.ofReal_toReal (hfin x)).symm
  rw [hrepr]
  rw [lintegral_eq_lintegral_meas_lt P.toMeasure
    (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg))
    (measurable_of_countable _).aemeasurable]
  rw [lintegral_eq_lintegral_meas_lt D.toMeasure
    (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg))
    (measurable_of_countable _).aemeasurable]
  apply lintegral_mono
  intro t
  apply toMeasure_le_of_isLowerSet P D h
  intro x y hxy hy
  exact lt_of_lt_of_le hy (hreal hxy)

/-- If `V` under `P` is stochastically at least `D` and `cdf D u ≤ cdf D' u` for every `u`, then `V`
under `P` is stochastically at least `D'`. -/
theorem StochGe.mono_law (h : StochGe P V D) (hD : ∀ u, cdf D u ≤ cdf D' u) : StochGe P V D' :=
  by
    intro u
    exact (h u).trans (hD u)
/-- If `V` under `P` is stochastically at least `D` and `ψ` is antitone, the expectation of
`ψ (V a)` under `P` is at most the expectation of `ψ` under `D`. -/
theorem StochGe.expectation_antitone (h : StochGe P V D) {ψ : ℚ≥0 → ℝ≥0∞} (hψ : Antitone ψ) :
    expectation P (fun a => ψ (V a)) ≤ expectation D ψ := by
  classical
  let : MeasurableSpace ℚ≥0 := ⊤
  let : MeasurableSingletonClass ℚ≥0 := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hCDF : ∀ u, (P.map V).toMeasure (Set.Iic u) ≤ D.toMeasure (Set.Iic u) := by
    intro u
    have hh := h u
    change eventProbability P (fun a => V a ≤ u) ≤ eventProbability D (fun x => x ≤ u) at hh
    rw [← eventProbability_map P V (fun x => x ≤ u),
      eventProbability_eq_toMeasure, eventProbability_eq_toMeasure] at hh
    exact hh
  change expectation P (fun a => ψ (V a)) ≤ expectation D ψ
  rw [← expectation_map P V ψ, expectation_eq_lintegral, expectation_eq_lintegral]
  have hre : ψ = fun x => ⨆ n : ℕ, min (ψ x) (n : ℝ≥0∞) := by
    funext x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  conv_lhs => rw [hre]
  rw [lintegral_iSup (fun _ => measurable_of_countable _) (by
    intro n m hnm x
    exact min_le_min_left _ (by exact_mod_cast hnm))]
  apply iSup_le
  intro n
  apply le_trans (lintegral_antitone_le (P.map V) D hCDF _ ?_ ?_)
  · exact lintegral_mono fun x => min_le_left _ _
  · intro x y hxy
    exact min_le_min_right _ (hψ hxy)
  · intro x
    exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
/-- Sequential products: draw `a` from `P`, then `b` from `K a`. If `V₁` under `P` is stochastically
at least `D₁` and, for every `a` with `V₁ a ≠ 0`, `V₂ a` under `K a` is stochastically at least
`D₂`, then the product `V₁ a * V₂ a b` is stochastically at least `mulLaw D₁ D₂`. -/
theorem StochGe.bind_mul {α β : Type*} (P : PMF α) (K : α → PMF β) (V₁ : α → ℚ≥0) (V₂ : α → β → ℚ≥0)
    {D₁ D₂ : PMF ℚ≥0} (h₁ : StochGe P V₁ D₁) (h₂ : ∀ a, V₁ a ≠ 0 → StochGe (K a) (V₂ a) D₂) :
    StochGe (P.bind fun a => (K a).map (Prod.mk a)) (fun x => V₁ x.1 * V₂ x.1 x.2) (mulLaw D₁ D₂) :=
  by
    classical
    intro u
    simp only [cdf, mulLaw, eventProbability_bind, eventProbability_map]
    refine le_trans (expectation_mono P fun a => ?_) (h₁.expectation_antitone ?_)
    · by_cases ha : V₁ a = 0
      · simp [ha, eventProbability]
      · have hh := (h₂ a ha).expectation_antitone
          (ψ := fun b => if V₁ a * b ≤ u then 1 else 0) (by
            intro b b' hbb
            dsimp only
            split_ifs with hb hb' <;> first
              | exact le_rfl
              | exact bot_le
              | exact False.elim (hb' ((mul_le_mul_right hbb _).trans hb)))
        simpa only [← eventProbability_eq_expectation] using hh
    · intro a a' haa
      exact eventProbability_mono_of_imp D₂ fun b hb => (mul_le_mul_left haa b).trans hb
/-- Sequential sums: draw `a` from `P`, then `b` from `K a`. If `V₁` under `P` is stochastically at
least `D₁` and, for every `a`, `V₂ a` under `K a` is stochastically at least `D₂`, then the sum
`V₁ a + V₂ a b` is stochastically at least `addLaw D₁ D₂`. -/
theorem StochGe.bind_add {α β : Type*} (P : PMF α) (K : α → PMF β) (V₁ : α → ℚ≥0) (V₂ : α → β → ℚ≥0)
    {D₁ D₂ : PMF ℚ≥0} (h₁ : StochGe P V₁ D₁) (h₂ : ∀ a, StochGe (K a) (V₂ a) D₂) :
    StochGe (P.bind fun a => (K a).map (Prod.mk a)) (fun x => V₁ x.1 + V₂ x.1 x.2) (addLaw D₁ D₂) :=
  by
    classical
    intro u
    simp only [cdf, addLaw, eventProbability_bind, eventProbability_map]
    refine le_trans (expectation_mono P fun a => ?_) (h₁.expectation_antitone ?_)
    · have hh := (h₂ a).expectation_antitone
        (ψ := fun b => if V₁ a + b ≤ u then 1 else 0) (by
          intro b b' hbb
          dsimp only
          split_ifs with hb hb' <;> first
            | exact le_rfl
            | exact bot_le
            | exact False.elim (hb' ((add_le_add_right hbb _).trans hb)))
      simpa only [← eventProbability_eq_expectation] using hh
    · intro a a' haa
      exact eventProbability_mono_of_imp D₂ fun b hb => (add_le_add_left haa b).trans hb
/-- The law of the product of two independent draws does not depend on their order. -/
theorem mulLaw_comm (D E : PMF ℚ≥0) : mulLaw D E = mulLaw E D := by
  unfold mulLaw
  simp only [PMF.map]
  rw [PMF.bind_comm]
  congr 1
  funext a
  congr 1
  funext b
  simp [mul_comm]

/-- The law of the product of three independent draws does not depend on the grouping:
`mulLaw (mulLaw A B) C = mulLaw A (mulLaw B C)`. -/
theorem mulLaw_assoc (A B C : PMF ℚ≥0) :
    mulLaw (mulLaw A B) C = mulLaw A (mulLaw B C) := by
  simp only [mulLaw, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, mul_assoc]

/-- The law of the sum of three independent draws does not depend on the grouping:
`addLaw (addLaw A B) C = addLaw A (addLaw B C)`. -/
theorem addLaw_assoc (A B C : PMF ℚ≥0) :
    addLaw (addLaw A B) C = addLaw A (addLaw B C) := by
  simp only [addLaw, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, add_assoc]

/-- The law of the product of four independent draws from `D` is the law of the product of two
independent draws from `mulLaw D D`. -/
theorem iidProd_four (D : PMF ℚ≥0) :
    iidProd D 4 = mulLaw (mulLaw D D) (mulLaw D D) := by
  have h : mulLaw D (PMF.pure 1) = D := by
    simp only [mulLaw, PMF.pure_map, mul_one, PMF.bind_pure]
  simp only [iidProd, h, mulLaw_assoc]

/-- The law of the sum of four independent draws from `D` is the law of the sum of two independent
draws from `addLaw D D`. -/
theorem iidSum_four (D : PMF ℚ≥0) :
    iidSum D 4 = addLaw (addLaw D D) (addLaw D D) := by
  have h : addLaw D (PMF.pure 0) = D := by
    simp only [addLaw, PMF.pure_map, add_zero, PMF.bind_pure]
  simp only [iidSum, h, addLaw_assoc]

/-- If `V` under `P` is stochastically at least `D` and `W (f a) = V a` on the support of `P`, then
`W` under `P.map f` is stochastically at least `D`. -/
theorem StochGe.map {α β : Type*} {P : PMF α} {V : α → ℚ≥0}
    {D : PMF ℚ≥0} (h : StochGe P V D) (f : α → β) (W : β → ℚ≥0)
    (hW : ∀ a ∈ P.support, W (f a) = V a) : StochGe (P.map f) W D := by
  intro u
  rw [eventProbability_map]
  exact (eventProbability_mono_of_support P
    (fun a ha hw => by simpa [hW a ha] using hw)).trans (h u)

/-- If `V` under `Q` is stochastically at least `D` and `W` agrees with `V` on the support of `Q`,
then `W` under `Q` is stochastically at least `D`. -/
theorem StochGe.congr_support {α : Type*} {Q : PMF α} {V W : α → ℚ≥0}
    {D : PMF ℚ≥0} (h : StochGe Q V D) (heq : ∀ a ∈ Q.support, W a = V a) :
    StochGe Q W D := by
  simpa only [PMF.map_id] using StochGe.map h id W heq

/-- If `V` under `Q` is stochastically at least `D`, the probability that `V` is strictly below `u`
is at most the probability that a draw from `D` is strictly below `u`. -/
theorem StochGe.eventProbability_lt_le {α : Type*} {Q : PMF α} {V : α → ℚ≥0} {D : PMF ℚ≥0}
    (h : StochGe Q V D) (u : ℚ≥0) :
    eventProbability Q (fun a => V a < u) ≤ eventProbability D (fun x => x < u) := by
  classical
  have hi : Antitone (fun x : ℚ≥0 => if x < u then (1 : ℝ≥0∞) else 0) := by
    intro a b hab
    by_cases hb : b < u
    · simp [hb, lt_of_le_of_lt hab hb]
    · simp [hb]
  have he := h.expectation_antitone hi
  rw [eventProbability_eq_tsum, eventProbability_eq_tsum]
  unfold expectation at he
  convert he using 1 <;> apply tsum_congr <;> intro a <;> split_ifs <;> simp_all

/-- If `V` under `Q` is stochastically at least `D`, the sum of `V` over `n` independent draws from
`Q` is stochastically at least the sum of `n` independent draws from `D`. -/
theorem StochGe.piPMF_sum {α : Type*} {n : ℕ} (Q : PMF α) (V : α → ℚ≥0)
    (D : PMF ℚ≥0) (h : StochGe Q V D) :
    StochGe (piPMF (fun _ : Fin n => Q)) (fun x => ∑ i, V (x i)) (iidSum D n) := by
  induction n with
  | zero =>
      intro u
      simp [piPMF, iidSum, cdf, eventProbability, PMF.pure_map]
  | succ n ih =>
      have hsum := StochGe.bind_add Q (fun _ => piPMF (fun _ : Fin n => Q)) V
        (fun _ x => ∑ i, V (x i)) h (fun _ => ih)
      have hm := StochGe.map hsum (fun z => Fin.cons z.1 z.2)
        (fun x => ∑ i, V (x i)) (by
          intro z _
          simp [Fin.sum_univ_succ])
      simpa only [piPMF, iidSum, PMF.map_bind, PMF.map_comp, Function.comp_def] using hm

/-- If `V` under `P` is stochastically at least `D`, the event `E` has probability at most `ε`, and
`min 1 (cdf D u + ε) ≤ cdf D' u` for every `u`, then the quantity that is `0` on `E` and `V`
elsewhere is stochastically at least `D'` (spec Theorem 3.1, second bullet). -/
theorem StochGe.of_event {α : Type*} (P : PMF α) (E : α → Prop) [DecidablePred E] (V : α → ℚ≥0)
    {D D' : PMF ℚ≥0} {ε : ℝ≥0∞} (hE : eventProbability P E ≤ ε) (hV : StochGe P V D)
    (hD' : ∀ u, min 1 (cdf D u + ε) ≤ cdf D' u) :
    StochGe P (fun a => if E a then 0 else V a) D' := by
  classical
  intro u
  apply le_trans (le_min (eventProbability_le_one _ _) ?_) (hD' u)
  calc
    eventProbability P (fun a => (if E a then 0 else V a) ≤ u) ≤
        eventProbability P (fun a => V a ≤ u) + eventProbability P E := by
      simp only [eventProbability_eq_expectation, expectation, ← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro a
      split_ifs <;> simp_all
    _ ≤ cdf D u + ε := add_le_add (hV u) hE

/-- Spec Corollary C′: if `μ.MGFConstant t K` holds with `0 ≤ t` and `X` is nonzero, the probability
that the output `Y` of `stage μ c X` has `sqNorm Y ≤ u * sqNorm X` is at most
`smallBallBound t K c u`. -/
theorem stage_smallBall_le (μ : EntryLaw) {t K : ℝ} (hK : μ.MGFConstant t K) (ht : 0 ≤ t)
    (c : ℕ) (X : Table f F) (hX : X ≠ 0) (u : ℚ≥0) :
    eventProbability (stage μ c X) (fun Y => (sqNorm Y : ℚ≥0) ≤ u * sqNorm X) ≤
      smallBallBound t K c u := by
  classical
  have hn : 0 < sqNorm X := Nat.pos_of_ne_zero (mt sqNorm_eq_zero_iff.mp hX)
  have hnR : 0 < (sqNorm X : ℝ) := by exact_mod_cast hn
  have hKpos : 0 < K := by
    obtain ⟨Y, hY⟩ := (stage μ 1 X).support_nonempty
    have hp : 0 < expectation (stage μ 1 X)
        (fun Y => ENNReal.ofReal (Real.exp (-t * (sqNorm Y : ℝ) / (sqNorm X : ℝ)))) :=
      lt_of_lt_of_le (ENNReal.mul_pos hY
        (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))) (ENNReal.le_tsum Y)
    have := hp.trans_le (stage_mgf_le μ hK 1 X hX)
    simpa using this
  apply le_min (eventProbability_le_one _ _)
  have hpoint :
      eventProbability (stage μ c X) (fun Y => (sqNorm Y : ℚ≥0) ≤ u * sqNorm X) ≤
        ENNReal.ofReal (Real.exp (t * (u : ℝ))) *
          expectation (stage μ c X)
            (fun Y => ENNReal.ofReal (Real.exp (-t * (sqNorm Y : ℝ) /
              (sqNorm X : ℝ)))) := by
    simp only [eventProbability_eq_expectation, expectation, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro Y
    rw [← mul_assoc, mul_comm (ENNReal.ofReal _) ((stage μ c X) Y), mul_assoc]
    apply mul_le_mul_right
    split_ifs with hY
    · have hYR : (sqNorm Y : ℝ) ≤ (u : ℝ) * (sqNorm X : ℝ) := by
        exact_mod_cast hY
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      apply ENNReal.one_le_ofReal.mpr
      apply Real.one_le_exp_iff.mpr
      have hd := (div_le_iff₀ hnR).mpr hYR
      have hm := mul_le_mul_of_nonneg_left hd ht
      rw [neg_mul, neg_div, mul_div_assoc]
      linarith
    · exact bot_le
  refine hpoint.trans ?_
  calc
    _ ≤ ENNReal.ofReal (Real.exp (t * (u : ℝ))) * ENNReal.ofReal K ^ c :=
      mul_le_mul_right (stage_mgf_le μ hK c X hX) _
    _ = ENNReal.ofReal (K ^ c * Real.exp (t * (u : ℝ))) := by
      rw [← ENNReal.ofReal_pow hKpos.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        mul_comm]

/-- Spec Corollary C′ as a domination statement: if `μ.MGFConstant t K` holds with `0 ≤ t` and `X`
is nonzero, the ratio `sqNorm Y / sqNorm X` for the output `Y` of `stage μ c X` is stochastically at
least every law `D` with `smallBallBound t K c u ≤ cdf D u` for all `u`. -/
theorem stage_stochGe (μ : EntryLaw) {t K : ℝ} (hK : μ.MGFConstant t K) (ht : 0 ≤ t) (c : ℕ)
    (X : Table f F) (hX : X ≠ 0) {D : PMF ℚ≥0} (hD : ∀ u, smallBallBound t K c u ≤ cdf D u) :
    StochGe (stage μ c X) (fun Y => (sqNorm Y : ℚ≥0) / sqNorm X) D := by
  intro u
  have hn : (0 : ℚ≥0) < sqNorm X := by
    exact_mod_cast Nat.pos_of_ne_zero (mt sqNorm_eq_zero_iff.mp hX)
  simpa only [div_le_iff₀ hn] using (stage_smallBall_le μ hK ht c X hX u).trans (hD u)

/-- The comparison laws for a check whose branches have `L` stages with `c` rows each and whose
final stage has `cT` rows. The parameters `t` and `K` are those of `MGFConstant`, and `ε` bounds the
probability of the event on which a branch contributes zero (see `StochGe.of_event`). -/
structure ComparisonData (t K : ℝ) (c cT L : ℕ) (ε : ℝ≥0∞) where
  /-- The comparison law for the squared-norm ratio of one branch stage. -/
  stageLaw : PMF ℚ≥0
  /-- The comparison law for the squared-norm ratio of the final stage. -/
  finalLaw : PMF ℚ≥0
  /-- The comparison law for the squared-norm ratio of a whole branch. -/
  branchLaw : PMF ℚ≥0
  /-- The distribution function of `stageLaw` is at least `smallBallBound t K c`. -/
  le_cdf_stageLaw : ∀ u, smallBallBound t K c u ≤ cdf stageLaw u
  /-- The distribution function of `finalLaw` is at least `smallBallBound t K cT`. -/
  le_cdf_finalLaw : ∀ u, smallBallBound t K cT u ≤ cdf finalLaw u
  /-- The distribution function of `branchLaw` is at least that of the product of `L` independent
  draws from `stageLaw`, plus `ε`, capped at `1`. -/
  le_cdf_branchLaw : ∀ u, min 1 (cdf (iidProd stageLaw L) u + ε) ≤ cdf branchLaw u

/-- The probability that the product of a draw from `C.finalLaw` with the sum of `g` independent
draws from `C.branchLaw` is less than `η`. -/
noncomputable def ComparisonData.failProb (C : ComparisonData t K c cT L ε) (g : ℕ)
    (η : ℚ≥0) : ℝ≥0∞ :=
  eventProbability (mulLaw C.finalLaw (iidSum C.branchLaw g)) (· < η)

end CertifiedProjections.MultiStage
