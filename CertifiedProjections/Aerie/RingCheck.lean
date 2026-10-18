/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.Params
import CertifiedProjections.MultiStage.Compose.RingCheck

/-!
# Aerie ring-equation check

The ring-equation check `ringCheck` consists of three stages whose entries are uniform on the
integers from `-b` to `b`, for `b = P.ringEntryBound`, separated by re-indexings (spec §5 and §7). A
`RingShape` gives the table shapes and the re-indexings, `ringCheckInt` is the same kernel over the
integers (`ringCheck_modOf`), and `RingAccept` is the acceptance predicate.

The main results are `ringCheck_accept_le` (a residual that is nonzero mod `q` is accepted with
probability at most `P.ringCheckError`), `ringCheck_reject_le` (a residual that is zero mod `q` is
rejected with probability at most `P.overflowError`), and the numerical bounds
`falcon512_ringCheckError_le` and `falcon1024_ringCheckError_le`.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.Aerie

open MultiStage

variable {c F : ℕ}

/-- Table shapes and re-indexings of the ring-equation check, whose three stages have `rows 0`,
`rows 1` and `rows 2` rows. Spec §5. -/
structure RingShape (rows : Fin 3 → ℕ) where
  /-- `f i` is the fan-in of stage `i`: the number of rows of its input table. -/
  f : Fin 3 → ℕ
  /-- `F i` is the number of columns of the input table of stage `i`. -/
  F : Fin 3 → ℕ
  /-- The re-indexing of the output of stage `0` as the input of stage `1`. -/
  e₁ : Fin (rows 0) × Fin (F 0) ≃ Fin (f 1) × Fin (F 1)
  /-- The re-indexing of the output of stage `1` as the input of stage `2`. -/
  e₂ : Fin (rows 1) × Fin (F 1) ≃ Fin (f 2) × Fin (F 2)

/-- The ring-equation check modulo `P.p`: three stages with entry law
`EntryLaw.uniform P.ringEntryBound` and `P.ringRows i` rows, each centered modulo `P.p`, with the
re-indexings `sh.e₁` and `sh.e₂` between them. Spec §5. -/
noncomputable def ringCheck (P : Params) (sh : RingShape P.ringRows) :
    TableKernel (sh.f 0) (sh.F 0) (P.ringRows 2) (sh.F 2) :=
  (stageMod P.p (EntryLaw.uniform P.ringEntryBound) (P.ringRows 0)).andThen
    (TableKernel.ofFun (reshape sh.e₁)) |>.andThen
    (stageMod P.p (EntryLaw.uniform P.ringEntryBound) (P.ringRows 1)) |>.andThen
    (TableKernel.ofFun (reshape sh.e₂)) |>.andThen
    (stageMod P.p (EntryLaw.uniform P.ringEntryBound) (P.ringRows 2))

/-- The ring-equation check over the integers: the same stages and re-indexings as `ringCheck`,
without centering. -/
noncomputable def ringCheckInt (P : Params) (sh : RingShape P.ringRows) :
    TableKernel (sh.f 0) (sh.F 0) (P.ringRows 2) (sh.F 2) :=
  (stage (EntryLaw.uniform P.ringEntryBound) (P.ringRows 0)).andThen
    (TableKernel.ofFun (reshape sh.e₁)) |>.andThen
    (stage (EntryLaw.uniform P.ringEntryBound) (P.ringRows 1)) |>.andThen
    (TableKernel.ofFun (reshape sh.e₂)) |>.andThen
    (stage (EntryLaw.uniform P.ringEntryBound) (P.ringRows 2))

/-- The acceptance predicate of the ring-equation check: the centered output `ctr P.p y` is zero mod
`P.q`. Spec Theorem 5.3. -/
def RingAccept (P : Params) (y : Table c F) : Prop :=
  ZeroMod P.q (MultiStage.ctr P.p y)

/-- `ringCheck P sh` is `ringCheckInt P sh` computed modulo `P.p`. -/
theorem ringCheck_modOf (P : Params) (sh : RingShape P.ringRows) :
    ModOf P.p (ringCheck P sh) (ringCheckInt P sh) := by
  unfold ringCheck ringCheckInt
  exact (((ModOf.stage.andThen
    (ModOf.ofFun (reshape sh.e₁) (fun _ => ctr_reshape.symm))).andThen
    ModOf.stage).andThen
    (ModOf.ofFun (reshape sh.e₂) (fun _ => ctr_reshape.symm))).andThen
    ModOf.stage

/-- The law `ringCheck P sh X` is the law of `ringCheckInt P sh X` with the output centered modulo
`P.p`. -/
private theorem ringCheck_eq_map (P : Params) (sh : RingShape P.ringRows)
    (X : Table (sh.f 0) (sh.F 0)) :
    ringCheck P sh X = (ringCheckInt P sh X).map (ctr P.p) := by
  have h : ringCheck P sh X = ringCheck P sh (ctr P.p X) := by
    unfold ringCheck TableKernel.andThen
    rw [stageMod_congr (show ctr P.p X = ctr P.p (ctr P.p X) from ctr_ctr.symm)]
  exact h.trans (ringCheck_modOf P sh X)

/-- `ringCheckInt P sh` satisfies the moment bound of order `P.overflowOrder` whose constant is the
product over the three stages of
`P.ringVariance ^ P.overflowOrder * chiSquareMoment (P.ringRows i) P.overflowOrder`. -/
private theorem ringCheckInt_momentBound (P : Params) (sh : RingShape P.ringRows) :
    MomentBound (ringCheckInt P sh) P.overflowOrder
      (∏ i, (P.ringVariance : ℝ≥0∞) ^ P.overflowOrder *
        (chiSquareMoment (P.ringRows i) P.overflowOrder : ℝ≥0∞)) := by
  have hs (i : Fin 3) := MomentBound.stage (f := sh.f i) (F := sh.F i)
    (EntryLaw.uniform P.ringEntryBound)
    (EntryLaw.uniform_symmetric _) (EntryLaw.uniform_momentDominated _)
    (P.ringRows i) P.overflowOrder
  have h := (((hs 0).andThen
    (MomentBound.ofFun (reshape sh.e₁) (fun _ => sqNorm_reshape) P.overflowOrder)).andThen
    (hs 1)).andThen
    (MomentBound.ofFun (reshape sh.e₂) (fun _ => sqNorm_reshape) P.overflowOrder) |>.andThen
    (hs 2)
  simpa [ringCheckInt, Params.ringVariance, Fin.prod_univ_succ, mul_assoc] using h

/-- If `P.Valid` holds, `ringCheckInt P sh` maps a table that is nonzero mod `P.q` to one that is
zero mod `P.q` with probability at most `P.falseZeroError`. -/
private theorem ringCheckInt_falseZeroBound (P : Params) (hP : P.Valid)
    (sh : RingShape P.ringRows) :
    FalseZeroBound (ringCheckInt P sh) P.q (P.falseZeroError : ℝ≥0∞) := by
  have hs (i : Fin 3) := FalseZeroBound.stage (f := sh.f i) (F := sh.F i)
    (EntryLaw.uniform P.ringEntryBound)
    (EntryLaw.uniform_atomBound _) hP.q_prime hP.ringEntryBound_lt (P.ringRows i)
  have h := (((hs 0).andThen
    (FalseZeroBound.ofFun (reshape sh.e₁) (fun _ => zeroMod_reshape.mp))).andThen
    (hs 1)).andThen
    (FalseZeroBound.ofFun (reshape sh.e₂) (fun _ => zeroMod_reshape.mp)) |>.andThen
    (hs 2)
  have hb : ((2 * P.ringEntryBound + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
  simpa [ringCheckInt, Params.falseZeroError, Fin.sum_univ_succ, add_assoc,
    ENNReal.coe_inv hb, Nat.cast_add, Nat.cast_mul, div_eq_mul_inv, inv_pow,
    ENNReal.inv_pow] using h

/-- If `P.Valid` holds, the overflow term of `MultiStage.ringCheck_accept_le`, for the moment
constant of `ringCheckInt_momentBound` and `H = P.residualSqNorm`, equals `P.overflowError`. -/
private theorem ringCheck_overflow_eq (P : Params) (hP : P.Valid) :
    (∏ i, (P.ringVariance : ℝ≥0∞) ^ P.overflowOrder *
      (chiSquareMoment (P.ringRows i) P.overflowOrder : ℝ≥0∞)) *
      (4 * P.residualSqNorm : ℝ≥0∞) ^ P.overflowOrder /
      (P.p : ℝ≥0∞) ^ (2 * P.overflowOrder) = (P.overflowError : ℝ≥0∞) := by
  have hp : (P.p : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hP.betaSq_lt))
  simp [Params.overflowError, ENNReal.coe_div (pow_ne_zero _ hp),
    Fin.prod_univ_succ, mul_comm]

/-- Soundness of the ring-equation check: if `P.Valid` holds, `sqNorm Δ ≤ P.residualSqNorm` (`H_Δ`)
and `Δ` is nonzero mod `P.q`, then `ringCheck P sh Δ` is accepted with probability at most
`P.ringCheckError`. Spec Theorem 5.3. -/
theorem ringCheck_accept_le (P : Params) (hP : P.Valid)
    (sh : RingShape P.ringRows) (Δ : Table (sh.f 0) (sh.F 0))
    (hH : sqNorm Δ ≤ P.residualSqNorm) (hΔ : ¬ ZeroMod P.q Δ) :
    eventProbability (ringCheck P sh Δ) (RingAccept P) ≤
      (P.ringCheckError : ℝ≥0∞) := by
  rw [ringCheck_eq_map]
  have h := MultiStage.ringCheck_accept_le (p := P.p)
    (ringCheckInt_momentBound P sh) (ringCheckInt_falseZeroBound P hP sh) Δ hH hΔ
  simpa [eventProbability, PMF.map_comp, Function.comp_def, RingAccept, ctr_ctr,
    ringCheck_overflow_eq P hP, Params.ringCheckError] using h

/-- If `X` is zero mod `q`, every table `Y` in the support of `stage μ c X` is zero mod `q`. -/
private theorem stage_preserves_zeroMod {f : ℕ} (μ : EntryLaw) (c q : ℕ)
    (X : Table f F) (hX : ZeroMod q X) (Y : Table c F)
    (hY : Y ∈ (stage μ c X).support) : ZeroMod q Y := by
  obtain ⟨C, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hY
  intro k φ
  change (q : ℤ) ∣ ∑ j, C k j * X j φ
  exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_right (hX j φ) _)

/-- If `g` maps tables that are zero mod `q` to tables that are zero mod `q`, then so does the
kernel `TableKernel.ofFun g`. -/
private theorem ofFun_preserves_zeroMod
    {f f' F' : ℕ} (q : ℕ) (g : Table f F → Table f' F')
    (hg : ∀ X, ZeroMod q X → ZeroMod q (g X))
    (X : Table f F) (hX : ZeroMod q X) (Y : Table f' F')
    (hY : Y ∈ (TableKernel.ofFun g X).support) : ZeroMod q Y := by
  have h : Y = g X := (PMF.mem_support_pure_iff _ _).mp hY
  exact h.symm ▸ hg X hX

/-- If `K₁` and `K₂` map every table that is zero mod `q` to tables that are zero mod `q`, then so
does `K₁.andThen K₂`. -/
private theorem andThen_preserves_zeroMod
    {f f₁ F₁ f₂ F₂ : ℕ} {K₁ : TableKernel f F f₁ F₁} {K₂ : TableKernel f₁ F₁ f₂ F₂}
    (q : ℕ)
    (h₁ : ∀ X, ZeroMod q X → ∀ Y ∈ (K₁ X).support, ZeroMod q Y)
    (h₂ : ∀ X, ZeroMod q X → ∀ Y ∈ (K₂ X).support, ZeroMod q Y)
    (X : Table f F) (hX : ZeroMod q X) (Y : Table f₂ F₂)
    (hY : Y ∈ (K₁.andThen K₂ X).support) : ZeroMod q Y := by
  obtain ⟨Z, hZ, hY⟩ := (PMF.mem_support_bind_iff _ _ _).mp hY
  exact h₂ Z (h₁ X hX Z hZ) Y hY

/-- If `X` is zero mod `P.q`, every table in the support of `ringCheckInt P sh X` is zero mod
`P.q`. -/
private theorem ringCheckInt_preserves_zeroMod (P : Params) (sh : RingShape P.ringRows) :
    ∀ X, ZeroMod P.q X → ∀ Y ∈ (ringCheckInt P sh X).support, ZeroMod P.q Y := by
  unfold ringCheckInt
  apply andThen_preserves_zeroMod
  · apply andThen_preserves_zeroMod
    · apply andThen_preserves_zeroMod
      · apply andThen_preserves_zeroMod
        · exact stage_preserves_zeroMod _ _ _
        · exact ofFun_preserves_zeroMod _ _ (fun _ => zeroMod_reshape.mpr)
      · exact stage_preserves_zeroMod _ _ _
    · exact ofFun_preserves_zeroMod _ _ (fun _ => zeroMod_reshape.mpr)
  · exact stage_preserves_zeroMod _ _ _

/-- If `P.Valid` holds, `sqNorm Δ ≤ P.residualSqNorm` and `Δ` is zero mod `P.q`, then
`ringCheck P sh Δ` is rejected with probability at most `P.overflowError`. Spec §7. -/
theorem ringCheck_reject_le (P : Params) (hP : P.Valid)
    (sh : RingShape P.ringRows) (Δ : Table (sh.f 0) (sh.F 0))
    (hH : sqNorm Δ ≤ P.residualSqNorm) (hΔ : ZeroMod P.q Δ) :
    eventProbability (ringCheck P sh Δ) (fun y => ¬ RingAccept P y) ≤
      (P.overflowError : ℝ≥0∞) := by
  rw [ringCheck_eq_map]
  have h := MultiStage.ringCheck_reject_le (p := P.p)
    (ringCheckInt_momentBound P sh) (ringCheckInt_preserves_zeroMod P sh) Δ hH hΔ
  simpa [eventProbability, PMF.map_comp, Function.comp_def, RingAccept, ctr_ctr,
    ringCheck_overflow_eq P hP] using h

set_option linter.style.longLine false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The product has 136 factors and is evaluated exactly.
/-- The numerical value of `chiSquareMoment 31 136`. -/
private theorem chiSquareMoment_31_136 : chiSquareMoment 31 136 = 182501420863195804697624017474596104683780512798380835422427466746223650266696630445478114202582582691062886658951603763456868106977175979596159803847626468630744802900656255714456964843961289821192967292497336483399598482972472067846473042639402733765431658942824974087649025022983551025390625 := by
  norm_num [chiSquareMoment, Finset.prod_range_succ]

set_option linter.style.longLine false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The product has 60 factors and is evaluated exactly.
/-- The numerical value of `chiSquareMoment 31 60`. -/
private theorem chiSquareMoment_31_60 : chiSquareMoment 31 60 = 9847397822184384399948332877008899842880330994988911611033043529127251994407531937123886783388185796733062744140625 := by
  norm_num [chiSquareMoment, Finset.prod_range_succ]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The inequality is between rational numbers with several thousand binary digits.
set_option exponentiation.threshold 272 in
/-- The ring-equation check error for Falcon-512 is at most `2^-142`. Spec §5. -/
theorem falcon512_ringCheckError_le : falcon512.ringCheckError ≤ 2⁻¹ ^ 142 := by
  have hv : falcon512.ringVariance = 52 := by
    norm_num [Params.ringVariance, falcon512]
  have hr (i : Fin 3) : falcon512.ringRows i = 31 := by
    fin_cases i <;> rfl
  simp only [Params.ringCheckError, Params.overflowError, Params.falseZeroError, hv, hr]
  change (((4 * falcon512.residualSqNorm : ℕ) : ℝ≥0) ^ 136 *
    (∏ _ : Fin 3, (52 : ℝ≥0) ^ 136 * (chiSquareMoment 31 136 : ℝ≥0))) /
    ((2 ^ 64 - 59 : ℕ) : ℝ≥0) ^ (2 * 136) +
    (∑ _ : Fin 3, (25⁻¹ : ℝ≥0) ^ 31) ≤ (2⁻¹ : ℝ≥0) ^ 142
  rw [chiSquareMoment_31_136]
  apply NNReal.coe_le_coe.mp
  push_cast
  norm_num [Params.residualSqNorm, falcon512]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The inequality is between rational numbers with several thousand binary digits.
/-- The ring-equation check error for Falcon-1024 is at most `2^-142`. Spec §5. -/
theorem falcon1024_ringCheckError_le : falcon1024.ringCheckError ≤ 2⁻¹ ^ 142 := by
  have hv : falcon1024.ringVariance = 52 := by
    norm_num [Params.ringVariance, falcon1024]
  have hr (i : Fin 3) : falcon1024.ringRows i = 31 := by
    fin_cases i <;> rfl
  simp only [Params.ringCheckError, Params.overflowError, Params.falseZeroError, hv, hr]
  change (((4 * falcon1024.residualSqNorm : ℕ) : ℝ≥0) ^ 60 *
    (∏ _ : Fin 3, (52 : ℝ≥0) ^ 60 * (chiSquareMoment 31 60 : ℝ≥0))) /
    ((2 ^ 64 - 59 : ℕ) : ℝ≥0) ^ (2 * 60) +
    (∑ _ : Fin 3, (25⁻¹ : ℝ≥0) ^ 31) ≤ (2⁻¹ : ℝ≥0) ^ 142
  rw [chiSquareMoment_31_60]
  apply NNReal.coe_le_coe.mp
  push_cast
  norm_num [Params.residualSqNorm, falcon1024]

end CertifiedProjections.Aerie
