/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.NormCheck
import CertifiedProjections.Aerie.RingCheck
import CertifiedProjections.Aerie.Lift
import CertifiedProjections.MultiStage.Compose.Moments
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Projection soundness and completeness

Spec Theorem 6.1, Corollary 6.2, Theorem 7.1 and Corollary 7.2.

`projectionCheck` runs the norm check and the ring-equation check independently, and `ProjectionBad`
is the condition on a source that the soundness theorem is about. Soundness is `projection_sound`:
both checks accept a source satisfying `ProjectionBad` with probability at most `normCheckError`. By
`exists_residual_eq_mul_of_not_projectionBad`, for a source that does not satisfy it and satisfies
the norm identity, the residual of every record is `q` times a vector with bounded entries.

For completeness, `normCheckInt_momentBound` gives the moment bound of the norm check with constant
`normMoment`, `normCheck_reject_le` derives from it a bound on the probability that the norm check
rejects an honest source, and `falcon512_honest_le` and `falcon1024_honest_le` evaluate this bound
for the two parameter sets. `projection_complete` bounds the probability that at least one of the
two checks rejects.
-/

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace CertifiedProjections.Aerie

open MultiStage

variable {N : ℕ}

/-- Run `normCheck` on `S` and `ringCheck` on `Δ` independently and output the pair of results. Spec
H1 and Theorem 6.1. -/
noncomputable def projectionCheck (P : Params) (nsh : NormShape) (rsh : RingShape P.ringRows)
    (S : Table (nsh.f 0) (nsh.F 0)) (Δ : Table (rsh.f 0) (rsh.F 0)) :
    PMF (Table finalRows (nsh.F 4) × Table (P.ringRows 2) (rsh.F 2)) :=
  (normCheck P.p nsh S).bind fun y => (ringCheck P rsh Δ).map fun z => (y, z)

/-- The first component of `projectionCheck P nsh rsh S Δ` has law `normCheck P.p nsh S`. -/
private theorem projectionCheck_map_fst (P : Params) (nsh : NormShape) (rsh : RingShape P.ringRows)
    (S : Table (nsh.f 0) (nsh.F 0)) (Δ : Table (rsh.f 0) (rsh.F 0)) :
    (projectionCheck P nsh rsh S Δ).map Prod.fst = normCheck P.p nsh S := by
  simp only [projectionCheck, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((normCheck P.p nsh S).bind fun a =>
    (ringCheck P rsh Δ).map (Function.const _ a)) = _
  simp only [PMF.map_const, PMF.bind_pure]

/-- The second component of `projectionCheck P nsh rsh S Δ` has law `ringCheck P rsh Δ`. -/
private theorem projectionCheck_map_snd (P : Params) (nsh : NormShape) (rsh : RingShape P.ringRows)
    (S : Table (nsh.f 0) (nsh.F 0)) (Δ : Table (rsh.f 0) (rsh.F 0)) :
    (projectionCheck P nsh rsh S Δ).map Prod.snd = ringCheck P rsh Δ := by
  simp only [projectionCheck, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((normCheck P.p nsh S).bind fun _ => (ringCheck P rsh Δ).map id) = _
  rw [PMF.map_id, PMF.bind_const]

/-- `ringCheck P sh` gives the same law on two inputs with the same centering modulo `P.p`. -/
private theorem ringCheck_congr (P : Params) (sh : RingShape P.ringRows)
    {X X' : Table (sh.f 0) (sh.F 0)} (h : MultiStage.ctr P.p X = MultiStage.ctr P.p X') :
    ringCheck P sh X = ringCheck P sh X' := by
  simp only [ringCheck, TableKernel.andThen]
  rw [stageMod_congr h]

/-- `normBranch p sh` gives the same law on two inputs with the same centering modulo `p`. -/
private theorem normBranch_congr (p : ℕ) (sh : NormShape)
    {X X' : Table (sh.f 0) (sh.F 0)} (h : MultiStage.ctr p X = MultiStage.ctr p X') :
    normBranch p sh X = normBranch p sh X' := by
  simp only [normBranch, TableKernel.andThen]
  rw [stageMod_congr h]

/-- `normCheck p sh` gives the same law on two inputs with the same centering modulo `p`. -/
private theorem normCheck_congr (p : ℕ) (sh : NormShape)
    {X X' : Table (sh.f 0) (sh.F 0)} (h : MultiStage.ctr p X = MultiStage.ctr p X') :
    normCheck p sh X = normCheck p sh X' := by
  simp only [normCheck, TableKernel.andThen, branches]
  simp_rw [normBranch_congr p sh h]

/-- Spec Theorem 6.1, the event `Bad`: either `src.normTableSqNorm P.p` is at least `P.soundSqNorm`
(`Q_S`), or it is below `Q_S`, the norm identity holds for every record and the residual of the
centered source is nonzero mod `P.q`. -/
def ProjectionBad (P : Params) (pub : PublicInput P.n N) (src : Source P.n N) : Prop :=
  P.soundSqNorm ≤ (src.normTableSqNorm P.p : ℚ≥0) ∨
  ((src.normTableSqNorm P.p : ℚ≥0) < P.soundSqNorm ∧ (∀ i, NormIdentity P pub src i) ∧
    ¬ ZeroMod P.q (residual pub (src.ctr P.p)))

/-- Soundness: assume `P.Valid`, `P.ringCheckError ≤ normCheckError`, `N ≤ P.maxSignatures`,
`nsh.FanInLe P`, `pub.Bounded P` and `src.S2Bounded P`. If `ProjectionBad P pub src` holds, both
checks accept with probability at most `normCheckError`. Spec Theorem 6.1. `eN` and `eR` place the
two sources in the input tables of the checks. -/
theorem projection_sound (P : Params) (hP : P.Valid) (hring : P.ringCheckError ≤ normCheckError)
    (hN : N ≤ P.maxSignatures) (nsh : NormShape) (hnsh : nsh.FanInLe P)
    (rsh : RingShape P.ringRows)
    (eN : Fin (2 * P.n) × Fin N ≃ Fin (nsh.f 0) × Fin (nsh.F 0))
    (eR : Fin P.n × Fin N ≃ Fin (rsh.f 0) × Fin (rsh.F 0))
    (pub : PublicInput P.n N) (hpub : pub.Bounded P) (src : Source P.n N)
    (hs2 : src.S2Bounded P) (hbad : ProjectionBad P pub src) :
    eventProbability
        (projectionCheck P nsh rsh (reshape eN src.normTable) (reshape eR (residual pub src)))
        (fun y => NormAccept P y.1 ∧ RingAccept P y.2) ≤ (normCheckError : ℝ≥0∞) := by
  rcases hbad with hlarge | ⟨hsmall, hid, hnonzero⟩
  · have hn := normCheck_accept_le P hP nsh hnsh (reshape eN src.normTable)
    have he : sqNorm (MultiStage.ctr P.p (reshape eN src.normTable)) =
        src.normTableSqNorm P.p := by
      rw [ctr_reshape, sqNorm_reshape, sqNorm_ctr_normTable hP.four_le_n]
    have hb := hn (by simpa only [he] using hlarge)
    calc
      _ ≤ eventProbability (projectionCheck P nsh rsh (reshape eN src.normTable)
          (reshape eR (residual pub src))) (fun y => NormAccept P y.1) :=
        eventProbability_mono_of_imp _ (fun _ h => h.1)
      _ = eventProbability (normCheck P.p nsh (reshape eN src.normTable)) (NormAccept P) := by
        rw [← eventProbability_map, projectionCheck_map_fst]
      _ ≤ _ := hb
  · have hs1 := natAbs_ctr_s1_le P hP pub src hs2 hid hsmall
    have hs2' := sum_sq_ctr_s2_le P hP pub src hs2 hid hsmall
    have hc := ctr_residual P hP pub src hpub hs1 hs2'
    have he : ringCheck P rsh (reshape eR (residual pub src)) =
        ringCheck P rsh (reshape eR (residual pub (src.ctr P.p))) := by
      apply ringCheck_congr
      rw [ctr_reshape, hc, ctr_reshape, ← hc, ctr_ctr]
    have hb := ringCheck_accept_le P hP rsh (reshape eR (residual pub (src.ctr P.p)))
      (by rw [sqNorm_reshape]; exact sqNorm_residual_le P hP hN pub src hpub hs1 hs2')
      (by simpa only [zeroMod_reshape] using hnonzero)
    calc
      _ ≤ eventProbability (projectionCheck P nsh rsh (reshape eN src.normTable)
          (reshape eR (residual pub src))) (fun y => RingAccept P y.2) :=
        eventProbability_mono_of_imp _ (fun _ h => h.2)
      _ = eventProbability (ringCheck P rsh (reshape eR (residual pub (src.ctr P.p))))
          (RingAccept P) := by rw [← eventProbability_map, projectionCheck_map_snd, he]
      _ ≤ (P.ringCheckError : ℝ≥0∞) := hb
      _ ≤ _ := ENNReal.coe_le_coe.mpr hring

/-- Assume `P.Valid`, `pub.Bounded P` and `src.S2Bounded P`. If the norm identity holds for every
record and `ProjectionBad P pub src` does not hold, then for every record `i` the residual of the
centered source is `P.q` times a vector `v` whose entries have absolute value at most
`P.residualEntryBound / P.q`, rounded down. Spec Corollary 6.2. -/
theorem exists_residual_eq_mul_of_not_projectionBad (P : Params) (hP : P.Valid)
    (pub : PublicInput P.n N) (hpub : pub.Bounded P)
    (src : Source P.n N) (hs2 : src.S2Bounded P) (hid : ∀ i, NormIdentity P pub src i)
    (hgood : ¬ ProjectionBad P pub src) (i : Fin N) :
    ∃ v : Fin P.n → ℤ, (∀ j, (v j).natAbs ≤ P.residualEntryBound / P.q) ∧
      ∀ j, residual pub (src.ctr P.p) j i = (P.q : ℤ) * v j := by
  classical
  have hsmall : (src.normTableSqNorm P.p : ℚ≥0) < P.soundSqNorm :=
    lt_of_not_ge (fun h => hgood (Or.inl h))
  have hz : ZeroMod P.q (residual pub (src.ctr P.p)) := by
    by_contra hn
    exact hgood (Or.inr ⟨hsmall, hid, hn⟩)
  choose v hv using fun j => hz j i
  refine ⟨v, ?_, hv⟩
  intro j
  have hb := natAbs_residual_le P hP pub src hpub
    (natAbs_ctr_s1_le P hP pub src hs2 hid hsmall)
    (sum_sq_ctr_s2_le P hP pub src hs2 hid hsmall) j i
  rw [hv j, Int.natAbs_mul, Int.natAbs_natCast] at hb
  exact (Nat.le_div_iff_mul_le hP.q_prime.pos).mpr (by simpa [Nat.mul_comm] using hb)

/-- Spec (7.1): the constant `M_t` in the `t`-th moment bound of the norm check
(`normCheckInt_momentBound`), with the ternary factor `(c/2)_k` written as
`chiSquareMoment c k / 2 ^ k`. -/
def normMoment (t : ℕ) : ℝ≥0 :=
  2⁻¹ ^ t * (chiSquareMoment finalRows t : ℝ≥0) *
    branchMoment numBranches
      (fun k => (2⁻¹ ^ k * (chiSquareMoment branchRows k : ℝ≥0)) ^ numBranchStages) t

/-- `normBranchInt sh` satisfies the `t`-th moment bound with constant
`(2⁻¹ ^ t * chiSquareMoment branchRows t) ^ numBranchStages`. -/
private theorem normBranchInt_momentBound (sh : NormShape) (t : ℕ) :
    MomentBound (normBranchInt sh) t
      (((2⁻¹ ^ t * (chiSquareMoment branchRows t : ℝ≥0)) ^ numBranchStages : ℝ≥0) : ℝ≥0∞) := by
  have hs {f F : ℕ} := MomentBound.stage (f := f) (F := F)
    EntryLaw.ternary EntryLaw.ternary_symmetric EntryLaw.ternary_momentDominated branchRows t
  have hr₁ := MomentBound.ofFun (reshape sh.e₁) (fun _ => sqNorm_reshape) t
  have hr₂ := MomentBound.ofFun (reshape sh.e₂) (fun _ => sqNorm_reshape) t
  have hr₃ := MomentBound.ofFun (reshape sh.e₃) (fun _ => sqNorm_reshape) t
  have hb := ((((((hs (f := sh.f 0)).andThen hr₁).andThen hs).andThen hr₂).andThen hs).andThen
    hr₃).andThen hs
  convert hb using 1 <;>
    simp [normBranchInt, numBranchStages, ENNReal.coe_pow, ENNReal.coe_mul,
      ENNReal.coe_inv, pow_succ, mul_assoc, div_eq_mul_inv, ENNReal.inv_pow]

/-- `normCheckInt sh` satisfies the `t`-th moment bound with constant `normMoment t`. Spec Theorem
7.1. -/
theorem normCheckInt_momentBound (sh : NormShape) (t : ℕ) :
    MomentBound (normCheckInt sh) t (normMoment t : ℝ≥0∞) := by
  have hb := MomentBound.branches (t := t) (fun (_ : Fin numBranches) k _ =>
    normBranchInt_momentBound sh k)
  have hr := MomentBound.ofFun (reshape sh.e₄) (fun _ => sqNorm_reshape) t
  have hs := MomentBound.stage (f := sh.f 4) (F := sh.F 4) EntryLaw.ternary
    EntryLaw.ternary_symmetric EntryLaw.ternary_momentDominated finalRows t
  convert (hb.andThen hr).andThen hs using 1 <;>
    simp [normCheckInt, normMoment, branchMoment, ENNReal.coe_pow, ENNReal.coe_mul,
    ENNReal.coe_inv, ENNReal.ofNNReal_finsetSum, ENNReal.ofNNReal_finsetProd,
    mul_comm, div_eq_mul_inv, ENNReal.inv_pow]

/-- If the centered source `ctr P.p S` has squared norm at most `P.honestSqNorm` (`H_S`), the norm
check rejects `S` with probability at most `normMoment t * P.honestSqNorm ^ t / P.acceptSqNorm ^ t`,
for every order `t`. Spec Theorem 7.1. -/
theorem normCheck_reject_le (P : Params) (sh : NormShape) (S : Table (sh.f 0) (sh.F 0))
    (hS : sqNorm (MultiStage.ctr P.p S) ≤ P.honestSqNorm) (t : ℕ) :
    eventProbability (normCheck P.p sh S) (fun y => ¬ NormAccept P y) ≤
      (normMoment t : ℝ≥0∞) * (P.honestSqNorm : ℝ≥0∞) ^ t /
        (P.acceptSqNorm : ℝ≥0∞) ^ t := by
  have hc : normCheck P.p sh S =
      (normCheckInt sh (MultiStage.ctr P.p S)).map (MultiStage.ctr P.p) := by
    rw [← normCheck_modOf P.p sh (MultiStage.ctr P.p S), ctr_ctr]
    exact normCheck_congr P.p sh ctr_ctr.symm
  rw [hc, eventProbability_map]
  calc
    _ ≤ eventProbability (normCheckInt sh (MultiStage.ctr P.p S))
        (fun y => P.acceptSqNorm < sqNorm y) := by
      apply eventProbability_mono_of_imp
      intro y hy
      have h : P.acceptSqNorm < sqNorm (MultiStage.ctr P.p (MultiStage.ctr P.p y)) :=
        lt_of_not_ge hy
      exact h.trans_le (by rw [ctr_ctr]; exact sqNorm_ctr_le)
    _ ≤ _ := (normCheckInt_momentBound sh t).tail_le _ _
    _ ≤ _ := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_right (pow_le_pow_left' (by exact_mod_cast hS) t) _

/-- Multiplying each constant `m k` by `a ^ k` multiplies `branchMoment g m t` by `a ^ t`. -/
private theorem branchMoment_scale {R : Type*} [CommSemiring R] (g t : ℕ)
    (m : ℕ → R) (a : R) :
    branchMoment g (fun k => a ^ k * m k) t = a ^ t * branchMoment g m t := by
  unfold branchMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hs : ∑ i, k i = t := Finset.Nat.mem_antidiagonalTuple.mp hk
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs]
  ring

/-- `branchMoment` commutes with the cast from `ℕ` to `ℝ≥0`. -/
private theorem branchMoment_cast (g t : ℕ) (m : ℕ → ℕ) :
    branchMoment g (fun k => (m k : ℝ≥0)) t =
      ((branchMoment (R := ℕ) g m t : ℕ) : ℝ≥0) := by
  simp only [branchMoment, Nat.cast_sum, Nat.cast_mul, Nat.cast_prod, Nat.cast_id]

/-- `normMoment t` is `2⁻¹ ^ (5 * t)` times the natural number
`chiSquareMoment 156 t * branchMoment 4 (fun k => chiSquareMoment 43 k ^ 4) t`. -/
private theorem normMoment_scale (t : ℕ) :
    normMoment t = (2⁻¹ : ℝ≥0) ^ (5 * t) *
      (chiSquareMoment 156 t * branchMoment 4 (fun k => chiSquareMoment 43 k ^ 4) t : ℕ) := by
  unfold normMoment
  have h (k : ℕ) : ((2⁻¹ : ℝ≥0) ^ k * (chiSquareMoment 43 k : ℝ≥0)) ^ 4 =
      ((2⁻¹ : ℝ≥0) ^ 4) ^ k * (chiSquareMoment 43 k ^ 4 : ℕ) := by
    simp only [mul_pow, ← pow_mul, Nat.cast_pow]
    rw [Nat.mul_comm k 4]
  simp_rw [h]
  rw [branchMoment_scale, branchMoment_cast]
  simp only [Nat.cast_mul, ← pow_mul]
  rw [show 5 * t = t + 4 * t by omega, pow_add]
  ring

set_option linter.style.longLine false in
/-- The numerical value of `branchMoment 4 (fun k => chiSquareMoment 43 k ^ 4) 46`. -/
private theorem branchMoment46_eq :
    branchMoment (R := ℕ) 4 (fun k => chiSquareMoment 43 k ^ 4) 46 =
      13355642651196160098550977970054657707278118074454064151428934547027062262844936317431704790070609603765446981414632116865481090739683426277581344861814286850512910359798078866216996789703993073566209185769609803381641867820975035669309916282915826232732128598063721314726841124028018876210826628282753066230892734709760000000000000000000000000000000000000 := by
  rw [branchMoment_eq_getD_branchMomentTable]
  decide +kernel

/-- For Falcon-512, the bound of `normCheck_reject_le` with `t = 46` on the probability that the
norm check rejects an honest source is at most `2^-129`. The inequality is stated with the
denominator `acceptSqNorm ^ 46` moved to the right-hand side. Spec Theorem 7.1. -/
theorem falcon512_honest_le :
    normMoment 46 * (falcon512.honestSqNorm : ℝ≥0) ^ 46 ≤
      2⁻¹ ^ 129 * (falcon512.acceptSqNorm : ℝ≥0) ^ 46 := by
  rw [normMoment_scale, branchMoment46_eq]
  norm_num [chiSquareMoment, Finset.prod_range_succ, Params.honestSqNorm, falcon512]

/-- For Falcon-1024, the bound of `normCheck_reject_le` with `t = 46` on the probability that the
norm check rejects an honest source is at most `2^-129`. The inequality is stated with the
denominator `acceptSqNorm ^ 46` moved to the right-hand side. Spec Theorem 7.1. -/
theorem falcon1024_honest_le :
    normMoment 46 * (falcon1024.honestSqNorm : ℝ≥0) ^ 46 ≤
      2⁻¹ ^ 129 * (falcon1024.acceptSqNorm : ℝ≥0) ^ 46 := by
  rw [normMoment_scale, branchMoment46_eq]
  norm_num [chiSquareMoment, Finset.prod_range_succ, Params.honestSqNorm, falcon1024]

/-- Completeness: assume `P.Valid` and `hhonest`, which says that the bound of `normCheck_reject_le`
with `t = P.honestOrder` is at most `2^-129`. If `ctr P.p S` has squared norm at most
`P.honestSqNorm`, `sqNorm Δ ≤ P.residualSqNorm` and `Δ` is zero mod `P.q`, then at least one of the
two checks rejects with probability at most `2⁻¹ ^ 129 + P.overflowError`. Spec Corollary 7.2. -/
theorem projection_complete (P : Params) (hP : P.Valid)
    (hhonest : normMoment P.honestOrder * (P.honestSqNorm : ℝ≥0) ^ P.honestOrder ≤
      2⁻¹ ^ 129 * (P.acceptSqNorm : ℝ≥0) ^ P.honestOrder)
    (nsh : NormShape) (rsh : RingShape P.ringRows)
    (S : Table (nsh.f 0) (nsh.F 0)) (hS : sqNorm (MultiStage.ctr P.p S) ≤ P.honestSqNorm)
    (Δ : Table (rsh.f 0) (rsh.F 0)) (hH : sqNorm Δ ≤ P.residualSqNorm)
    (hΔ : ZeroMod P.q Δ) :
    eventProbability (projectionCheck P nsh rsh S Δ)
        (fun y => ¬ (NormAccept P y.1 ∧ RingAccept P y.2)) ≤
      ((2⁻¹ ^ 129 + P.overflowError : ℝ≥0) : ℝ≥0∞) := by
  have hn : eventProbability (normCheck P.p nsh S) (fun y => ¬ NormAccept P y) ≤
      ((2⁻¹ ^ 129 : ℝ≥0) : ℝ≥0∞) := by
    apply (normCheck_reject_le P nsh S hS P.honestOrder).trans
    apply ENNReal.div_le_of_le_mul
    exact_mod_cast hhonest
  have hr := ringCheck_reject_le P hP rsh Δ hH hΔ
  calc
    _ = eventProbability (projectionCheck P nsh rsh S Δ)
        (fun y => ¬ NormAccept P y.1 ∨ ¬ RingAccept P y.2) := by
      apply eventProbability_congr
      intro y
      exact not_and_or
    _ ≤ eventProbability (projectionCheck P nsh rsh S Δ) (fun y => ¬ NormAccept P y.1) +
        eventProbability (projectionCheck P nsh rsh S Δ) (fun y => ¬ RingAccept P y.2) :=
      eventProbability_le_add _ _ _ _ (fun _ h => h)
    _ = eventProbability (normCheck P.p nsh S) (fun y => ¬ NormAccept P y) +
        eventProbability (ringCheck P rsh Δ) (fun y => ¬ RingAccept P y) := by
      rw [← eventProbability_map _ Prod.fst (fun y => ¬ NormAccept P y), projectionCheck_map_fst,
        ← eventProbability_map _ Prod.snd (fun y => ¬ RingAccept P y), projectionCheck_map_snd]
    _ ≤ _ := by
      simpa only [ENNReal.coe_add] using add_le_add hn hr

end CertifiedProjections.Aerie
