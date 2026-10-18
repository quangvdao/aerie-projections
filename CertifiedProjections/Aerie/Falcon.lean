/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.Cores
import CertifiedProjections.Aerie.Geometry

/-!
# The projection theorem for Falcon-512 and Falcon-1024

`FalconWitness P pub src` says that the integer source `src` is a Falcon witness for the public
input `pub` (spec §1): every record satisfies the norm identity over the integers, every padding
record is zero, and every record satisfies the ring equation with an integer quotient.

Soundness, in the form of the success criterion of spec §1, is
`projection_sound_of_not_falconWitness`: if the centered `s2` coefficients are bounded (H3(a)), the
norm identity holds modulo `p` (H4) and the centered source is not a Falcon witness, then both
checks accept with probability at most `normCheckError`. Completeness is
`projection_complete_of_falconWitness`.

`falcon512_projection_sound`, `falcon1024_projection_sound`, `falcon512_projection_complete` and
`falcon1024_projection_complete` state the two results for the two parameter sets and the shapes of
the protocol, without further hypotheses on the parameters. They hold for every number of records
that the protocol admits after padding (spec F §6.2): `2 ^ (2 + R)` with `R ≤ 14` for Falcon-512,
and `2 ^ (1 + R)` with `R ≤ 15` for Falcon-1024. The number of signatures before padding is
`pub.numLive`. The probability is over uniform seeds `s : G.CoreSeeds P` of all cores of both
checks, which is spec hypothesis H1, and the event is about `G.outputs P pub src s`, the outputs
that the two checks compute from the source with the cores of `s`.

These theorems do not use `Aerie/Sampling.lean`. They say nothing about how the protocol derives
the cores from its transcript.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.Aerie

open MultiStage

variable {N : ℕ}

/-- The integer source `src` is a Falcon witness for `pub`. Spec §1. -/
structure FalconWitness (P : Params) (pub : PublicInput P.n N) (src : Source P.n N) : Prop where
  /-- The norm identity over the integers: the squares of the `s1`, `s2` and slack coefficients of a
  record sum to `P.betaSq` if the record is live and to `0` otherwise. Spec F (2.2). -/
  normIdentity : ∀ i : Fin N,
    (∑ j, src.s1 i j ^ 2 + ∑ j, src.s2 i j ^ 2 + ∑ k, src.e i k ^ 2 : ℤ) =
      if i.val < pub.numLive then (P.betaSq : ℤ) else 0
  /-- Every coefficient of a padding record is zero. -/
  padding : ∀ i : Fin N, pub.numLive ≤ i.val →
    (∀ j, src.s1 i j = 0) ∧ (∀ j, src.s2 i j = 0) ∧ ∀ k, src.e i k = 0
  /-- The ring equation `s1 + h ⊛ s2 - q * v = c` holds over the integers for an integer quotient
  `v`. Spec F (2.1). -/
  ringEquation : ∀ i : Fin N, ∃ v : Fin P.n → ℤ,
    ∀ j, src.s1 i j + negacyclicConv (pub.h i) (src.s2 i) j - (P.q : ℤ) * v j = pub.c i j

/-- Assume `P.Valid`, `pub.Bounded P` and `src.S2Bounded P`. If the norm identity holds modulo `P.p`
for every record and `ProjectionBad P pub src` does not hold, the centered source is a Falcon
witness. Spec Corollary 6.2. -/
theorem falconWitness_of_not_projectionBad (P : Params) (hP : P.Valid)
    (pub : PublicInput P.n N) (hpub : pub.Bounded P)
    (src : Source P.n N) (hs2 : src.S2Bounded P) (hid : ∀ i, NormIdentity P pub src i)
    (hgood : ¬ ProjectionBad P pub src) :
    FalconWitness P pub (src.ctr P.p) := by
  have hsmall : (src.normTableSqNorm P.p : ℚ≥0) < P.soundSqNorm :=
    lt_of_not_ge (fun h => hgood (Or.inl h))
  refine ⟨?_, padding_eq_zero P hP pub src hs2 hid hsmall, ?_⟩
  · intro i
    have h := congrArg (Nat.cast : ℕ → ℤ)
      (normIdentity_lift P hP pub src hs2 hid hsmall i)
    simpa [Source.ctr, sq_abs] using h
  · intro i
    obtain ⟨v, _, hv⟩ :=
      exists_residual_eq_mul_of_not_projectionBad P hP pub hpub src hs2 hid hgood i
    refine ⟨v, fun j => ?_⟩
    have h := hv j
    dsimp [residual] at h
    linarith

/-- Soundness, as the success criterion of spec §1: under the hypotheses of `projection_sound` on
the parameters and shapes, if `src.S2Bounded P` holds, the norm identity holds modulo `P.p` for
every record, and the centered source is not a Falcon witness, then both checks accept with
probability at most `normCheckError`. -/
theorem projection_sound_of_not_falconWitness (P : Params) (hP : P.Valid)
    (hring : P.ringCheckError ≤ normCheckError)
    (hN : N ≤ P.maxSignatures) (nsh : NormShape) (hnsh : nsh.FanInLe P)
    (rsh : RingShape P.ringRows)
    (eN : Fin (2 * P.n) × Fin N ≃ Fin (nsh.f 0) × Fin (nsh.F 0))
    (eR : Fin P.n × Fin N ≃ Fin (rsh.f 0) × Fin (rsh.F 0))
    (pub : PublicInput P.n N) (hpub : pub.Bounded P) (src : Source P.n N)
    (hs2 : src.S2Bounded P) (hid : ∀ i, NormIdentity P pub src i)
    (hnot : ¬ FalconWitness P pub (src.ctr P.p)) :
    eventProbability
        (projectionCheck P nsh rsh (reshape eN src.normTable) (reshape eR (residual pub src)))
        (fun y => NormAccept P y.1 ∧ RingAccept P y.2) ≤ (normCheckError : ℝ≥0∞) := by
  apply projection_sound P hP hring hN nsh hnsh rsh eN eR pub hpub src hs2
  by_contra hgood
  exact hnot (falconWitness_of_not_projectionBad P hP pub hpub src hs2 hid hgood)

/-- Completeness for a Falcon witness: under the hypotheses of `projection_complete` on the
parameters, if `N ≤ P.maxSignatures`, `pub.Bounded P` holds and `src` is a Falcon witness, then at
least one of the two checks rejects with probability at most `2⁻¹ ^ 129 + P.overflowError`. Spec
Corollary 7.2. -/
theorem projection_complete_of_falconWitness (P : Params) (hP : P.Valid)
    (hhonest : normMoment P.honestOrder * (P.honestSqNorm : ℝ≥0) ^ P.honestOrder ≤
      2⁻¹ ^ 129 * (P.acceptSqNorm : ℝ≥0) ^ P.honestOrder)
    (hN : N ≤ P.maxSignatures) (nsh : NormShape) (rsh : RingShape P.ringRows)
    (eN : Fin (2 * P.n) × Fin N ≃ Fin (nsh.f 0) × Fin (nsh.F 0))
    (eR : Fin P.n × Fin N ≃ Fin (rsh.f 0) × Fin (rsh.F 0))
    (pub : PublicInput P.n N) (hpub : pub.Bounded P) (src : Source P.n N)
    (hw : FalconWitness P pub src) :
    eventProbability
        (projectionCheck P nsh rsh (reshape eN src.normTable) (reshape eR (residual pub src)))
        (fun y => ¬ (NormAccept P y.1 ∧ RingAccept P y.2)) ≤
      ((2⁻¹ ^ 129 + P.overflowError : ℝ≥0) : ℝ≥0∞) := by
  have hid (i : Fin N) :
      ∑ j, (src.s1 i j).natAbs ^ 2 + ∑ j, (src.s2 i j).natAbs ^ 2 +
        ∑ k, (src.e i k).natAbs ^ 2 ≤ P.betaSq := by
    have h := hw.normIdentity i
    have hcast : ((∑ j, (src.s1 i j).natAbs ^ 2 + ∑ j, (src.s2 i j).natAbs ^ 2 +
        ∑ k, (src.e i k).natAbs ^ 2 : ℕ) : ℤ) ≤ (P.betaSq : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
      rw [h]
      split_ifs <;> omega
    exact_mod_cast hcast
  have hcoeff {m : ℕ} (a : Fin m → ℤ) (ha : ∑ j, (a j).natAbs ^ 2 ≤ P.betaSq)
      (j : Fin m) : (a j).natAbs ≤ Nat.sqrt P.betaSq := by
    apply Nat.le_sqrt'.mpr
    exact (Finset.single_le_sum (fun k _ => Nat.zero_le ((a k).natAbs ^ 2))
      (Finset.mem_univ j)).trans ha
  have hcenter (z : ℤ) (hz : z.natAbs ≤ Nat.sqrt P.betaSq) : centeredMod P.p z = z := by
    have hlt := hP.residualEntry_lt
    have hle := hP.residualEntry_le
    let : NeZero P.p := ⟨by omega⟩
    apply (ZMod.valMinAbs_spec _ _).mpr
    refine ⟨rfl, ?_⟩
    change -(P.p : ℤ) < z * 2 ∧ z * 2 ≤ (P.p : ℤ)
    omega
  have hs1 (i : Fin N) (j : Fin P.n) :
      (src.s1 i j).natAbs ≤ Nat.sqrt P.betaSq :=
    hcoeff (src.s1 i) (by have := hid i; omega) j
  have hs2 (i : Fin N) : ∑ j, (src.s2 i j).natAbs ^ 2 ≤ P.betaSq := by
    have := hid i
    omega
  have hc1 (i : Fin N) (j : Fin P.n) : centeredMod P.p (src.s1 i j) = src.s1 i j :=
    hcenter _ (hs1 i j)
  have hc2 (i : Fin N) (j : Fin P.n) : centeredMod P.p (src.s2 i j) = src.s2 i j :=
    hcenter _ (hcoeff (src.s2 i) (hs2 i) j)
  have hce (i : Fin N) (k : Fin 4) : centeredMod P.p (src.e i k) = src.e i k :=
    hcenter _ (hcoeff (src.e i) (by have := hid i; omega) k)
  have hctr : src.ctr P.p = src := by
    cases src
    simp_all [Source.ctr]
  apply projection_complete P hP hhonest nsh rsh
  · rw [ctr_reshape, sqNorm_reshape, sqNorm_ctr_normTable hP.four_le_n]
    unfold Source.normTableSqNorm
    simp only [hc1, hce]
    calc
      _ ≤ ∑ _i : Fin N, P.betaSq := Finset.sum_le_sum fun i _ => by
        have := hid i
        omega
      _ = N * P.betaSq := by simp
      _ ≤ P.honestSqNorm := Nat.mul_le_mul_right _ hN
  · rw [sqNorm_reshape, ← hctr]
    apply sqNorm_residual_le P hP hN pub src hpub
    · simpa only [hc1] using hs1
    · simpa only [hc2] using hs2
  · rw [zeroMod_reshape]
    intro j i
    obtain ⟨v, hv⟩ := hw.ringEquation i
    refine ⟨v j, ?_⟩
    have h := hv j
    dsimp [residual]
    linarith

namespace Geometry

/-- The seeds of all cores of both checks of the protocol: the sixteen cores of the branch stages
and the core of the final stage of the norm check, and the three cores of the ring-equation check.
Spec F §6.3. -/
abbrev CoreSeeds (G : Geometry) (P : Params) : Type :=
  NormCoreSeeds (G.normShape P.n) × RingCoreSeeds P (G.ringShape P)

/-- The outputs of the two checks of the protocol for the seeds `s`: the norm source and the
residual are placed in the input tables of the checks, multiplied stage by stage by the cores of
`s`, and centered modulo `P.p`. Spec F §6.3. -/
def outputs (G : Geometry) (P : Params) (pub : PublicInput P.n G.numRecords)
    (src : Source P.n G.numRecords) (s : G.CoreSeeds P) :
    Table finalRows ((G.normShape P.n).F 4) × Table (P.ringRows 2) ((G.ringShape P).F 2) :=
  (MultiStage.ctr P.p (normProjection (G.normShape P.n) s.1
      (reshape (G.normPlacement P.n) src.normTable)),
    MultiStage.ctr P.p (ringProjection P (G.ringShape P) s.2
      (reshape (G.ringPlacement P) (residual pub src))))

/-- The law `G.projectionCheck P pub src` is the law of `G.outputs P pub src s` for uniform seeds
`s`. Spec H1. -/
theorem projectionCheck_eq_map_outputs (G : Geometry) (P : Params)
    (pub : PublicInput P.n G.numRecords) (src : Source P.n G.numRecords) :
    G.projectionCheck P pub src =
      (PMF.uniformOfFintype (G.CoreSeeds P)).map (G.outputs P pub src) :=
  projectionCheck_eq_map P _ _ _ _

/-- The probability, over uniform seeds, of an event of the outputs is its probability under
`G.projectionCheck P pub src`. -/
theorem eventProbability_outputs (G : Geometry) (P : Params)
    (pub : PublicInput P.n G.numRecords) (src : Source P.n G.numRecords)
    (event : Table finalRows ((G.normShape P.n).F 4) ×
      Table (P.ringRows 2) ((G.ringShape P).F 2) → Prop) :
    eventProbability (PMF.uniformOfFintype (G.CoreSeeds P))
        (fun s => event (G.outputs P pub src s)) =
      eventProbability (G.projectionCheck P pub src) event := by
  rw [projectionCheck_eq_map_outputs]
  simp only [eventProbability, PMF.map_comp]
  rfl

end Geometry

/-- Soundness for Falcon-512 with `2 ^ (2 + R)` records, `R ≤ 14`. Assume that the public
coefficients are at most `6144` in absolute value, that the centered `s2` coefficients are at most
`2047` in absolute value, and that the norm identity holds modulo `p` for every record. If the
centered source is not a Falcon witness, then both checks of the protocol accept with probability
at most `2^-136` over uniform seeds of all cores. Spec Theorem 6.1 and Corollary 6.2. -/
theorem falcon512_projection_sound {R : ℕ} (hR : R ≤ 14)
    (pub : PublicInput falcon512.n (falcon512Geometry R).numRecords)
    (hpub : pub.Bounded falcon512)
    (src : Source falcon512.n (falcon512Geometry R).numRecords)
    (hs2 : src.S2Bounded falcon512) (hid : ∀ i, NormIdentity falcon512 pub src i)
    (hnot : ¬ FalconWitness falcon512 pub (src.ctr falcon512.p)) :
    eventProbability (PMF.uniformOfFintype ((falcon512Geometry R).CoreSeeds falcon512))
        (fun s => NormAccept falcon512 ((falcon512Geometry R).outputs falcon512 pub src s).1 ∧
          RingAccept falcon512 ((falcon512Geometry R).outputs falcon512 pub src s).2) ≤
      (2⁻¹ : ℝ≥0∞) ^ 136 := by
  refine ((falcon512Geometry R).eventProbability_outputs falcon512 pub src
    (fun y => NormAccept falcon512 y.1 ∧ RingAccept falcon512 y.2)).trans_le ?_
  have hring : falcon512.ringCheckError ≤ normCheckError :=
    falcon512_ringCheckError_le.trans (by
      apply NNReal.coe_le_coe.mp
      norm_num [normCheckError])
  simpa only [Geometry.projectionCheck, normCheckError, ENNReal.coe_pow,
    ENNReal.coe_inv_two] using
    projection_sound_of_not_falconWitness falcon512 falcon512_valid hring
      (falcon512Geometry_numRecords_le hR) _ (falcon512Geometry_fanInLe hR) _
      ((falcon512Geometry R).normPlacement falcon512.n)
      ((falcon512Geometry R).ringPlacement falcon512) pub hpub src hs2 hid hnot

/-- Soundness for Falcon-1024 with `2 ^ (1 + R)` records, `R ≤ 15`. Assume that the public
coefficients are at most `6144` in absolute value, that the centered `s2` coefficients are at most
`2047` in absolute value, and that the norm identity holds modulo `p` for every record. If the
centered source is not a Falcon witness, then both checks of the protocol accept with probability
at most `2^-136` over uniform seeds of all cores. Spec Theorem 6.1 and Corollary 6.2. -/
theorem falcon1024_projection_sound {R : ℕ} (hR : R ≤ 15)
    (pub : PublicInput falcon1024.n (falcon1024Geometry R).numRecords)
    (hpub : pub.Bounded falcon1024)
    (src : Source falcon1024.n (falcon1024Geometry R).numRecords)
    (hs2 : src.S2Bounded falcon1024) (hid : ∀ i, NormIdentity falcon1024 pub src i)
    (hnot : ¬ FalconWitness falcon1024 pub (src.ctr falcon1024.p)) :
    eventProbability (PMF.uniformOfFintype ((falcon1024Geometry R).CoreSeeds falcon1024))
        (fun s => NormAccept falcon1024 ((falcon1024Geometry R).outputs falcon1024 pub src s).1 ∧
          RingAccept falcon1024 ((falcon1024Geometry R).outputs falcon1024 pub src s).2) ≤
      (2⁻¹ : ℝ≥0∞) ^ 136 := by
  refine ((falcon1024Geometry R).eventProbability_outputs falcon1024 pub src
    (fun y => NormAccept falcon1024 y.1 ∧ RingAccept falcon1024 y.2)).trans_le ?_
  have hring : falcon1024.ringCheckError ≤ normCheckError :=
    falcon1024_ringCheckError_le.trans (by
      apply NNReal.coe_le_coe.mp
      norm_num [normCheckError])
  simpa only [Geometry.projectionCheck, normCheckError, ENNReal.coe_pow,
    ENNReal.coe_inv_two] using
    projection_sound_of_not_falconWitness falcon1024 falcon1024_valid hring
      (falcon1024Geometry_numRecords_le hR) _ (falcon1024Geometry_fanInLe hR) _
      ((falcon1024Geometry R).normPlacement falcon1024.n)
      ((falcon1024Geometry R).ringPlacement falcon1024) pub hpub src hs2 hid hnot

/-- Completeness for Falcon-512 with `2 ^ (2 + R)` records, `R ≤ 14`: if the public
coefficients are at most `6144` in absolute value and the source is a Falcon witness, then at least
one of the two checks of the protocol rejects with probability at most `2^-129 + 2^-142` over
uniform seeds of all cores. Spec Corollary 7.2 gives `2^-129 + overflowError`, and `overflowError`
is at most `2^-142`. -/
theorem falcon512_projection_complete {R : ℕ} (hR : R ≤ 14)
    (pub : PublicInput falcon512.n (falcon512Geometry R).numRecords)
    (hpub : pub.Bounded falcon512)
    (src : Source falcon512.n (falcon512Geometry R).numRecords)
    (hw : FalconWitness falcon512 pub src) :
    eventProbability (PMF.uniformOfFintype ((falcon512Geometry R).CoreSeeds falcon512))
        (fun s => ¬ (NormAccept falcon512 ((falcon512Geometry R).outputs falcon512 pub src s).1 ∧
            RingAccept falcon512 ((falcon512Geometry R).outputs falcon512 pub src s).2)) ≤
      (2⁻¹ : ℝ≥0∞) ^ 129 + 2⁻¹ ^ 142 := by
  refine ((falcon512Geometry R).eventProbability_outputs falcon512 pub src
    (fun y => ¬ (NormAccept falcon512 y.1 ∧ RingAccept falcon512 y.2))).trans_le ?_
  have hov : falcon512.overflowError ≤ (2⁻¹ : ℝ≥0) ^ 142 :=
    (le_add_of_nonneg_right (zero_le : 0 ≤ falcon512.falseZeroError)).trans
      falcon512_ringCheckError_le
  have h := projection_complete_of_falconWitness falcon512 falcon512_valid
    falcon512_honest_le (falcon512Geometry_numRecords_le hR) _ _
    ((falcon512Geometry R).normPlacement falcon512.n)
    ((falcon512Geometry R).ringPlacement falcon512) pub hpub src hw
  apply h.trans
  simpa only [ENNReal.coe_add, ENNReal.coe_pow, ENNReal.coe_inv_two] using
    ENNReal.coe_le_coe.mpr (add_le_add (le_refl ((2⁻¹ : ℝ≥0) ^ (129 : ℕ))) hov)

/-- Completeness for Falcon-1024 with `2 ^ (1 + R)` records, `R ≤ 15`: if the public
coefficients are at most `6144` in absolute value and the source is a Falcon witness, then at least
one of the two checks of the protocol rejects with probability at most `2^-129 + 2^-142` over
uniform seeds of all cores. Spec Corollary 7.2 gives `2^-129 + overflowError`, and `overflowError`
is at most `2^-142`. -/
theorem falcon1024_projection_complete {R : ℕ} (hR : R ≤ 15)
    (pub : PublicInput falcon1024.n (falcon1024Geometry R).numRecords)
    (hpub : pub.Bounded falcon1024)
    (src : Source falcon1024.n (falcon1024Geometry R).numRecords)
    (hw : FalconWitness falcon1024 pub src) :
    eventProbability (PMF.uniformOfFintype ((falcon1024Geometry R).CoreSeeds falcon1024))
        (fun s => ¬ (NormAccept falcon1024 ((falcon1024Geometry R).outputs falcon1024 pub src s).1 ∧
            RingAccept falcon1024 ((falcon1024Geometry R).outputs falcon1024 pub src s).2)) ≤
      (2⁻¹ : ℝ≥0∞) ^ 129 + 2⁻¹ ^ 142 := by
  refine ((falcon1024Geometry R).eventProbability_outputs falcon1024 pub src
    (fun y => ¬ (NormAccept falcon1024 y.1 ∧ RingAccept falcon1024 y.2))).trans_le ?_
  have hov : falcon1024.overflowError ≤ (2⁻¹ : ℝ≥0) ^ 142 :=
    (le_add_of_nonneg_right (zero_le : 0 ≤ falcon1024.falseZeroError)).trans
      falcon1024_ringCheckError_le
  have h := projection_complete_of_falconWitness falcon1024 falcon1024_valid
    falcon1024_honest_le (falcon1024Geometry_numRecords_le hR) _ _
    ((falcon1024Geometry R).normPlacement falcon1024.n)
    ((falcon1024Geometry R).ringPlacement falcon1024) pub hpub src hw
  apply h.trans
  simpa only [ENNReal.coe_add, ENNReal.coe_pow, ENNReal.coe_inv_two] using
    ENNReal.coe_le_coe.mpr (add_le_add (le_refl ((2⁻¹ : ℝ≥0) ^ (129 : ℕ))) hov)

end CertifiedProjections.Aerie
