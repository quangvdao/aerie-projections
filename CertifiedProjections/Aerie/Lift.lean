/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.Params
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Integer lift and residual bound

Sources, public inputs, the residual and the norm identity (spec §2), the lift of the norm identity
to the integers (spec Lemma 4.1) and the bound on the integer residual (spec Lemma 4.2).

A record is one signature slot. Record `i` of a `Source` holds the signature polynomials `s1 i` and
`s2 i` and four slack coefficients `e i`; record `i` of a `PublicInput` holds the public polynomials
`h i` and `c i`. The first `numLive` records are live and the rest are padding. The definitions are
`negacyclicConv`, `residual` and `NormIdentity`. The main results are `normIdentity_lift` (the norm
identity modulo `p` holds over the integers for the centered coefficients), `natAbs_residual_le` and
`sqNorm_residual_le` (bounds on the residual of the centered source), and `ctr_residual` (centering
the residual gives the residual of the centered source).
-/

open scoped BigOperators NNReal

namespace CertifiedProjections.Aerie

open MultiStage

variable {n N : ℕ}

/-- The source for `N` records with ring degree `n`: for each record, the signature polynomials `s1`
and `s2` and four slack coefficients `e`. Spec §2 Sources. -/
structure Source (n N : ℕ) where
  /-- `s1 i j` is coefficient `j` of the first signature polynomial of record `i`. -/
  s1 : Fin N → Fin n → ℤ
  /-- `s2 i j` is coefficient `j` of the second signature polynomial of record `i`. -/
  s2 : Fin N → Fin n → ℤ
  /-- `e i k` is the `k`-th of the four slack coefficients of record `i` (see `NormIdentity`). -/
  e : Fin N → Fin 4 → ℤ

/-- The public input for `N` records with ring degree `n`: for each record, the public polynomials
`h` and `c`, and the number of live records. Spec §2. -/
structure PublicInput (n N : ℕ) where
  /-- `h i j` is coefficient `j` of the public polynomial `h` of record `i`. -/
  h : Fin N → Fin n → ℤ
  /-- `c i j` is coefficient `j` of the public polynomial `c` of record `i`. -/
  c : Fin N → Fin n → ℤ
  /-- The number of live records: record `i` is live if `i < numLive` and padding otherwise. -/
  numLive : ℕ

/-- Coefficient `j` of the product in `ℤ[X]/(X^n + 1)` of the polynomials with coefficients `a` and
`b`. Spec (2.1). -/
def negacyclicConv {n : ℕ} (a b : Fin n → ℤ) (j : Fin n) : ℤ :=
  ∑ k : Fin n, ∑ l : Fin n,
    if k.val + l.val = j.val then a k * b l
    else if k.val + l.val = j.val + n then -(a k * b l) else 0

namespace Source

/-- Center every coefficient of `s1`, `s2` and `e` modulo `p`. Spec Lemma 4.1. -/
def ctr (p : ℕ) (src : Source n N) : Source n N where
  s1 i j := centeredMod p (src.s1 i j)
  s2 i j := centeredMod p (src.s2 i j)
  e i k := centeredMod p (src.e i k)

/-- The sum over all records of the squares of the centered `s1` and `e` coefficients, `𝓔(S)`. By
`sqNorm_ctr_normTable` it is the squared norm of the centered `normTable`. Spec §2. -/
def normTableSqNorm (p : ℕ) (src : Source n N) : ℕ :=
  ∑ i, (∑ j, (centeredMod p (src.s1 i j)).natAbs ^ 2 +
    ∑ k, (centeredMod p (src.e i k)).natAbs ^ 2)

/-- The input table of the norm check, with one column per record and `2 * n` rows: rows `j < n`
hold the coefficients of `s1`, rows `n` to `n + 3` hold the four slack coefficients, and the
remaining rows are zero. Spec §2 Sources. -/
def normTable (src : Source n N) : Table (2 * n) N :=
  Matrix.of fun j i =>
    if hj : j.val < n then src.s1 i ⟨j.val, hj⟩
    else if hk : j.val - n < 4 then src.e i ⟨j.val - n, hk⟩ else 0

/-- Every centered `s2` coefficient has absolute value at most `P.s2Bound`. Spec H3(a). -/
def S2Bounded (P : Params) (src : Source P.n N) : Prop :=
  ∀ i j, (centeredMod P.p (src.s2 i j)).natAbs ≤ P.s2Bound

end Source

/-- Every coefficient of `pub.h` and `pub.c` has absolute value at most `P.publicBound`. Spec §2
public inputs. -/
def PublicInput.Bounded (P : Params) (pub : PublicInput P.n N) : Prop :=
  ∀ i j, (pub.h i j).natAbs ≤ P.publicBound ∧ (pub.c i j).natAbs ≤ P.publicBound

/-- The residual `s1 + h ⊛ s2 − c`, where `⊛` is `negacyclicConv`, with coefficients as rows and
records as columns. Spec (2.1). -/
def residual (pub : PublicInput n N) (src : Source n N) : Table n N :=
  Matrix.of fun j i => src.s1 i j + negacyclicConv (pub.h i) (src.s2 i) j - pub.c i j

/-- The norm identity for record `i`, modulo `P.p`: the sum of the squares of the `s1`, `s2` and `e`
coefficients of the record is congruent to `P.betaSq` if the record is live (`i < pub.numLive`) and
to `0` otherwise. Spec (2.2). -/
def NormIdentity (P : Params) (pub : PublicInput P.n N) (src : Source P.n N)
    (i : Fin N) : Prop :=
  (∑ j, src.s1 i j ^ 2 + ∑ j, src.s2 i j ^ 2 + ∑ k, src.e i k ^ 2 : ℤ) ≡
    (if i.val < pub.numLive then (P.betaSq : ℤ) else 0) [ZMOD (P.p : ℤ)]

/-- If `4 ≤ n`, the squared norm of the centered `src.normTable` is `src.normTableSqNorm p`. -/
theorem sqNorm_ctr_normTable (hn : 4 ≤ n) (p : ℕ) (src : Source n N) :
    sqNorm (MultiStage.ctr p src.normTable) = src.normTableSqNorm p := by
  classical
  unfold sqNorm Source.normTableSqNorm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [MultiStage.ctr, Matrix.map_apply, Source.normTable, Matrix.of_apply]
  rw [show 2 * n = n + n by omega, Fin.sum_univ_add]
  have hfirst : (∑ j : Fin n, (centeredMod p
      (if hj : (Fin.castAdd n j).val < n then src.s1 i ⟨(Fin.castAdd n j).val, hj⟩
      else if hk : (Fin.castAdd n j).val - n < 4 then
        src.e i ⟨(Fin.castAdd n j).val - n, hk⟩ else 0)).natAbs ^ 2) =
      ∑ j, (centeredMod p (src.s1 i j)).natAbs ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Fin.castAdd, j.isLt]
  rw [hfirst]
  congr 1
  have hsecond : (∑ j : Fin n, (centeredMod p
      (if hj : (Fin.natAdd n j).val < n then src.s1 i ⟨(Fin.natAdd n j).val, hj⟩
      else if hk : (Fin.natAdd n j).val - n < 4 then
        src.e i ⟨(Fin.natAdd n j).val - n, hk⟩ else 0)).natAbs ^ 2) =
      ∑ j : Fin n, (centeredMod p
        (if hk : j.val < 4 then src.e i ⟨j.val, hk⟩ else 0)).natAbs ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp
  rw [hsecond]
  let f : ℕ → ℕ := fun t => (centeredMod p
    (if hk : t < 4 then src.e i ⟨t, hk⟩ else 0)).natAbs ^ 2
  change (∑ j : Fin n, f j.val) = _
  have hn4 : n = 4 + (n - 4) := by omega
  have hsplit : (∑ j : Fin n, f j.val) =
      (∑ j : Fin 4, f j.val) + ∑ j : Fin (n - 4), f (4 + j.val) := by
    conv_lhs => rw [hn4, Fin.sum_univ_add]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [hsplit]
  have hz : centeredMod p 0 = 0 := by simp [centeredMod]
  have hright : (∑ j : Fin (n - 4), f (4 + j.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [f, show ¬ 4 + j.val < 4 by omega, hz]
  rw [hright, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [f, j.isLt]

/-- If `P.Valid` and `src.S2Bounded P` hold, the norm identity holds modulo `P.p` for every record,
and `src.normTableSqNorm P.p < P.soundSqNorm`, then for the centered coefficients the norm identity
of record `i` holds as an equality of natural numbers. Spec Lemma 4.1. -/
theorem normIdentity_lift (P : Params) (hP : P.Valid) (pub : PublicInput P.n N)
    (src : Source P.n N) (hs2 : src.S2Bounded P) (hid : ∀ i, NormIdentity P pub src i)
    (hS : (src.normTableSqNorm P.p : ℚ≥0) < P.soundSqNorm) (i : Fin N) :
    ∑ j, (centeredMod P.p (src.s1 i j)).natAbs ^ 2 +
      ∑ j, (centeredMod P.p (src.s2 i j)).natAbs ^ 2 +
      ∑ k, (centeredMod P.p (src.e i k)).natAbs ^ 2 =
        if i.val < pub.numLive then P.betaSq else 0 := by
  classical
  let A := ∑ j, (centeredMod P.p (src.s1 i j)).natAbs ^ 2
  let B := ∑ j, (centeredMod P.p (src.s2 i j)).natAbs ^ 2
  let E := ∑ k, (centeredMod P.p (src.e i k)).natAbs ^ 2
  have hAE : A + E ≤ src.normTableSqNorm P.p := by
    change (∑ j, (centeredMod P.p (src.s1 i j)).natAbs ^ 2) +
      (∑ k, (centeredMod P.p (src.e i k)).natAbs ^ 2) ≤ _
    unfold Source.normTableSqNorm
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hB : B ≤ P.n * P.s2Bound ^ 2 := by
    calc
      B ≤ ∑ _j : Fin P.n, P.s2Bound ^ 2 :=
        Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left (hs2 i j) 2
      _ = _ := by simp
  have hlt : A + B + E < P.p := by
    have hn : A + B + E ≤ src.normTableSqNorm P.p + P.n * P.s2Bound ^ 2 := by omega
    have hbound := (Nat.cast_le (α := ℚ≥0)).mpr hn
    rw [Nat.cast_add (src.normTableSqNorm P.p) (P.n * P.s2Bound ^ 2)] at hbound
    have hadd : (src.normTableSqNorm P.p : ℚ≥0) + ((P.n * P.s2Bound ^ 2 : ℕ) : ℚ≥0) <
        P.soundSqNorm + ((P.n * P.s2Bound ^ 2 : ℕ) : ℚ≥0) :=
      add_lt_add_left (α := ℚ≥0) hS ((P.n * P.s2Bound ^ 2 : ℕ) : ℚ≥0)
    have hltq : ((A + B + E : ℕ) : ℚ≥0) < (P.p : ℚ≥0) :=
      lt_of_le_of_lt hbound (lt_trans hadd hP.lift)
    exact (Nat.cast_lt (α := ℚ≥0)).mp hltq
  have hsq (z : ℤ) : ((z.natAbs ^ 2 : ℕ) : ℤ) = z ^ 2 := by
    simp [sq_abs]
  have hsqmod (z : ℤ) : ((z.natAbs ^ 2 : ℕ) : ZMod P.p) = (z : ZMod P.p) ^ 2 := by
    rw [← Int.cast_natCast (z.natAbs ^ 2), hsq, Int.cast_pow]
  have hcast : ((A + B + E : ℕ) : ZMod P.p) =
      ((∑ j, src.s1 i j ^ 2 + ∑ j, src.s2 i j ^ 2 + ∑ k, src.e i k ^ 2 : ℤ) : ZMod P.p) := by
    dsimp [A, B, E]
    simp only [Nat.cast_add, Nat.cast_sum, hsqmod,
      Int.cast_add, Int.cast_sum, Int.cast_pow, centeredMod_intCast]
  have hid' := (ZMod.intCast_eq_intCast_iff _ _ P.p).mpr (hid i)
  have hmod : A + B + E ≡ (if i.val < pub.numLive then P.betaSq else 0) [MOD P.p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [hcast, hid']
    split_ifs <;> simp
  have hbeta := hP.betaSq_lt
  exact hmod.eq_of_lt_of_lt hlt (by split_ifs <;> omega)

/-- Under the hypotheses of `normIdentity_lift`, every centered `s1` coefficient has absolute value
at most `Nat.sqrt P.betaSq`. Spec Lemma 4.1. -/
theorem natAbs_ctr_s1_le (P : Params) (hP : P.Valid) (pub : PublicInput P.n N)
    (src : Source P.n N) (hs2 : src.S2Bounded P) (hid : ∀ i, NormIdentity P pub src i)
    (hS : (src.normTableSqNorm P.p : ℚ≥0) < P.soundSqNorm) (i : Fin N) (j : Fin P.n) :
    (centeredMod P.p (src.s1 i j)).natAbs ≤ Nat.sqrt P.betaSq := by
  have h := normIdentity_lift P hP pub src hs2 hid hS i
  have hj : (centeredMod P.p (src.s1 i j)).natAbs ^ 2 ≤
      ∑ j, (centeredMod P.p (src.s1 i j)).natAbs ^ 2 :=
    Finset.single_le_sum (f := fun j => (centeredMod P.p (src.s1 i j)).natAbs ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  apply Nat.le_sqrt'.mpr
  split_ifs at h <;> omega

/-- Under the hypotheses of `normIdentity_lift`, every centered slack coefficient has absolute value
at most `Nat.sqrt P.betaSq`. Spec Lemma 4.1. -/
theorem natAbs_ctr_e_le (P : Params) (hP : P.Valid) (pub : PublicInput P.n N)
    (src : Source P.n N) (hs2 : src.S2Bounded P) (hid : ∀ i, NormIdentity P pub src i)
    (hS : (src.normTableSqNorm P.p : ℚ≥0) < P.soundSqNorm) (i : Fin N) (k : Fin 4) :
    (centeredMod P.p (src.e i k)).natAbs ≤ Nat.sqrt P.betaSq := by
  have h := normIdentity_lift P hP pub src hs2 hid hS i
  have hk : (centeredMod P.p (src.e i k)).natAbs ^ 2 ≤
      ∑ k, (centeredMod P.p (src.e i k)).natAbs ^ 2 :=
    Finset.single_le_sum (f := fun k => (centeredMod P.p (src.e i k)).natAbs ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  apply Nat.le_sqrt'.mpr
  split_ifs at h <;> omega

/-- Under the hypotheses of `normIdentity_lift`, the squares of the centered `s2` coefficients of
record `i` sum to at most `P.betaSq`. Spec Lemma 4.1. -/
theorem sum_sq_ctr_s2_le (P : Params) (hP : P.Valid) (pub : PublicInput P.n N)
    (src : Source P.n N) (hs2 : src.S2Bounded P) (hid : ∀ i, NormIdentity P pub src i)
    (hS : (src.normTableSqNorm P.p : ℚ≥0) < P.soundSqNorm) (i : Fin N) :
    ∑ j, (centeredMod P.p (src.s2 i j)).natAbs ^ 2 ≤ P.betaSq := by
  have h := normIdentity_lift P hP pub src hs2 hid hS i
  split_ifs at h <;> omega

/-- Under the hypotheses of `normIdentity_lift`, every centered coefficient of a padding record
(`pub.numLive ≤ i`) is zero. Spec Lemma 4.1. -/
theorem padding_eq_zero (P : Params) (hP : P.Valid) (pub : PublicInput P.n N)
    (src : Source P.n N) (hs2 : src.S2Bounded P) (hid : ∀ i, NormIdentity P pub src i)
    (hS : (src.normTableSqNorm P.p : ℚ≥0) < P.soundSqNorm) (i : Fin N)
    (hi : pub.numLive ≤ i.val) :
    (∀ j, centeredMod P.p (src.s1 i j) = 0) ∧
      (∀ j, centeredMod P.p (src.s2 i j) = 0) ∧
      (∀ k, centeredMod P.p (src.e i k) = 0) := by
  have h := normIdentity_lift P hP pub src hs2 hid hS i
  rw [if_neg (by omega)] at h
  have zero_of_sum {m : ℕ} (a : Fin m → ℤ) (ha : ∑ j, (a j).natAbs ^ 2 = 0) :
      ∀ j, a j = 0 := by
    intro j
    have hj : (a j).natAbs ^ 2 ≤ ∑ j, (a j).natAbs ^ 2 :=
      Finset.single_le_sum (f := fun j => (a j).natAbs ^ 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have : (a j).natAbs = 0 := by nlinarith [hj]
    exact Int.natAbs_eq_zero.mp this
  exact ⟨zero_of_sum _ (by omega), zero_of_sum _ (by omega), zero_of_sum _ (by omega)⟩

/-- If every coefficient of `a` has absolute value at most `H`, every coefficient of
`negacyclicConv a b` has absolute value at most `H` times the sum of the absolute values of the
coefficients of `b`. -/
private theorem natAbs_negacyclicConv_le {n : ℕ} (a b : Fin n → ℤ) (H : ℕ)
    (ha : ∀ k, (a k).natAbs ≤ H) (j : Fin n) :
    (negacyclicConv a b j).natAbs ≤ H * ∑ l, (b l).natAbs := by
  classical
  unfold negacyclicConv
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ l : Fin n, (∑ k : Fin n,
      if k.val + l.val = j.val then a k * b l
      else if k.val + l.val = j.val + n then -(a k * b l) else 0).natAbs :=
        Int.natAbs_sum_le _ _
    _ ≤ ∑ l : Fin n, H * (b l).natAbs := by
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : l.val ≤ j.val
      · let k₀ : Fin n := ⟨j.val - l.val, by omega⟩
        have hsum : (∑ k : Fin n,
            if k.val + l.val = j.val then a k * b l
            else if k.val + l.val = j.val + n then -(a k * b l) else 0) =
            a k₀ * b l := by
          rw [Finset.sum_eq_single k₀]
          · simp [k₀, Nat.sub_add_cancel hl]
          · intro k _ hk
            have hv : k.val ≠ k₀.val := fun h => hk (Fin.ext h)
            simp only [k₀] at hv
            have h1 : k.val + l.val ≠ j.val := by omega
            have h2 : k.val + l.val ≠ j.val + n := by omega
            simp [h1, h2]
          · simp
        rw [hsum, Int.natAbs_mul]
        exact Nat.mul_le_mul_right _ (ha k₀)
      · let k₀ : Fin n := ⟨j.val + n - l.val, by omega⟩
        have hsum : (∑ k : Fin n,
            if k.val + l.val = j.val then a k * b l
            else if k.val + l.val = j.val + n then -(a k * b l) else 0) =
            -(a k₀ * b l) := by
          rw [Finset.sum_eq_single k₀]
          · have h1 : k₀.val + l.val ≠ j.val := by dsimp [k₀]; omega
            have h2 : k₀.val + l.val = j.val + n := by dsimp [k₀]; omega
            simp only [if_neg h1, if_pos h2]
          · intro k _ hk
            have hv : k.val ≠ k₀.val := fun h => hk (Fin.ext h)
            simp only [k₀] at hv
            have h1 : k.val + l.val ≠ j.val := by omega
            have h2 : k.val + l.val ≠ j.val + n := by omega
            simp [h1, h2]
          · simp
        rw [hsum, Int.natAbs_neg, Int.natAbs_mul]
        exact Nat.mul_le_mul_right _ (ha k₀)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- If `P.Valid` and `pub.Bounded P` hold, every centered `s1` coefficient has absolute value at
most `Nat.sqrt P.betaSq`, and the squares of the centered `s2` coefficients of each record sum to at
most `P.betaSq`, then every entry of the residual of the centered source has absolute value at most
`P.residualEntryBound`. Spec Lemma 4.2. -/
theorem natAbs_residual_le (P : Params) (hP : P.Valid)
    (pub : PublicInput P.n N) (src : Source P.n N) (hpub : pub.Bounded P)
    (hs1 : ∀ i j, (centeredMod P.p (src.s1 i j)).natAbs ≤ Nat.sqrt P.betaSq)
    (hs2 : ∀ i, ∑ j, (centeredMod P.p (src.s2 i j)).natAbs ^ 2 ≤ P.betaSq)
    (j : Fin P.n) (i : Fin N) :
    (residual pub (src.ctr P.p) j i).natAbs ≤ P.residualEntryBound := by
  have hc := natAbs_negacyclicConv_le (pub.h i)
    (fun k => centeredMod P.p (src.s2 i k)) P.publicBound (fun k => (hpub i k).1) j
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin P.n))
    (fun _ => (1 : ℕ)) (fun k => (centeredMod P.p (src.s2 i k)).natAbs)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hcs
  have hc2 : (negacyclicConv (pub.h i)
      (fun k => centeredMod P.p (src.s2 i k)) j).natAbs ^ 2 ≤
      P.publicBound ^ 2 * P.n * P.betaSq := by
    calc
      _ ≤ (P.publicBound * ∑ k, (centeredMod P.p (src.s2 i k)).natAbs) ^ 2 :=
        Nat.pow_le_pow_left hc 2
      _ = P.publicBound ^ 2 * (∑ k, (centeredMod P.p (src.s2 i k)).natAbs) ^ 2 :=
        mul_pow _ _ _
      _ ≤ P.publicBound ^ 2 * (P.n * P.betaSq) :=
        Nat.mul_le_mul_left _ (hcs.trans (Nat.mul_le_mul_left _ (hs2 i)))
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have hc3 : (negacyclicConv (pub.h i)
      (fun k => centeredMod P.p (src.s2 i k)) j).natAbs ≤
      P.residualEntryBound - Nat.sqrt P.betaSq - P.publicBound := by
    have h := hc2.trans hP.residualEntry_sq
    nlinarith
  change (centeredMod P.p (src.s1 i j) +
    negacyclicConv (pub.h i) (fun k => centeredMod P.p (src.s2 i k)) j -
    pub.c i j).natAbs ≤ _
  have htri := Int.natAbs_add_le (centeredMod P.p (src.s1 i j))
    (negacyclicConv (pub.h i) (fun k => centeredMod P.p (src.s2 i k)) j)
  have htri2 := Int.natAbs_sub_le
    (centeredMod P.p (src.s1 i j) +
      negacyclicConv (pub.h i) (fun k => centeredMod P.p (src.s2 i k)) j)
    (pub.c i j)
  have := hs1 i j
  have := (hpub i j).2
  have := hP.residualEntry_le
  omega

/-- Under the hypotheses of `natAbs_residual_le`, if `N ≤ P.maxSignatures` then the residual of the
centered source has squared norm at most `P.residualSqNorm` (`H_Δ`). Spec Lemma 4.2. -/
theorem sqNorm_residual_le (P : Params) (hP : P.Valid) (hN : N ≤ P.maxSignatures)
    (pub : PublicInput P.n N) (src : Source P.n N) (hpub : pub.Bounded P)
    (hs1 : ∀ i j, (centeredMod P.p (src.s1 i j)).natAbs ≤ Nat.sqrt P.betaSq)
    (hs2 : ∀ i, ∑ j, (centeredMod P.p (src.s2 i j)).natAbs ^ 2 ≤ P.betaSq) :
    sqNorm (residual pub (src.ctr P.p)) ≤ P.residualSqNorm := by
  unfold sqNorm Params.residualSqNorm
  calc
    _ ≤ ∑ _j : Fin P.n, ∑ _i : Fin N, P.residualEntryBound ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      exact Nat.pow_le_pow_left (natAbs_residual_le P hP pub src hpub hs1 hs2 j i) 2
    _ = P.n * (N * P.residualEntryBound ^ 2) := by simp
    _ ≤ _ := by
      have := Nat.mul_le_mul_right (P.n * P.residualEntryBound ^ 2) hN
      nlinarith

/-- Under the hypotheses of `natAbs_residual_le`, centering the residual of `src` modulo `P.p` gives
the residual of the centered source. Spec Lemma 4.2. -/
theorem ctr_residual (P : Params) (hP : P.Valid)
    (pub : PublicInput P.n N) (src : Source P.n N) (hpub : pub.Bounded P)
    (hs1 : ∀ i j, (centeredMod P.p (src.s1 i j)).natAbs ≤ Nat.sqrt P.betaSq)
    (hs2 : ∀ i, ∑ j, (centeredMod P.p (src.s2 i j)).natAbs ^ 2 ≤ P.betaSq) :
    MultiStage.ctr P.p (residual pub src) = residual pub (src.ctr P.p) := by
  have hp : P.p ≠ 0 := by have := hP.residualEntry_lt; omega
  let : NeZero P.p := ⟨hp⟩
  ext j i
  change centeredMod P.p (residual pub src j i) = residual pub (src.ctr P.p) j i
  unfold centeredMod
  apply (ZMod.valMinAbs_spec _ _).mpr
  constructor
  · simp [residual, Source.ctr, negacyclicConv, Int.cast_sum, Int.cast_ite,
      Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg]
  · have hb := natAbs_residual_le P hP pub src hpub hs1 hs2 j i
    have hp := hP.residualEntry_lt
    have hbound : 2 * (residual pub (src.ctr P.p) j i).natAbs < P.p := by omega
    change -(P.p : ℤ) < residual pub (src.ctr P.p) j i * 2 ∧
      residual pub (src.ctr P.p) j i * 2 ≤ (P.p : ℤ)
    omega

end CertifiedProjections.Aerie
