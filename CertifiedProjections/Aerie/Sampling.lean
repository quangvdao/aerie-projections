/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.EntryLaw

/-!
# From uniform bytes to core entries

The protocol derives the entries of the cores from bytes (spec F §6.3). This file shows that the two
maps give the entry laws of the two checks when the bytes are uniform.

`ternaryOfByte b` is the four entries of a norm core read from the byte `b`, one per bit pair. By
`map_ternaryOfByte`, for a uniform byte they are four independent draws from the ternary law.

A byte is accepted for a core of the ring-equation check if it is less than `250`, and
`uniformOfByte b` is the entry read from the accepted byte `b`. By `filter_byte_lt`, a uniform byte
conditioned on being accepted is uniform on the `250` accepted values, and by `map_uniformOfByte`
the entry is then uniform on the integers from `-12` to `12`.

Each statement is about one byte. The theorems of `Aerie/Falcon.lean` do not use them: they take the
entries of the cores to be independent with these laws (spec hypothesis H1). How the protocol
derives the bytes from its transcript, their order within a row of a core, and the bytes read after
a rejected byte are not formalized.
-/

namespace CertifiedProjections.Aerie

open MultiStage

/-- The four entries of a norm core read from the byte `b`: entry `i` is read from bits `2 * i` and
`2 * i + 1`, counted from the least significant. The pair `00` gives `-1`, the pair `11` gives `1`,
and the pairs `01` and `10` give `0`. Spec F §6.3. -/
def ternaryOfByte (b : Fin 256) (i : Fin 4) : ℤ :=
  sparseBit (b.val.testBit (2 * i.val), b.val.testBit (2 * i.val + 1))

/-- The four entries read from a uniform byte are independent draws from the ternary law. -/
theorem map_ternaryOfByte :
    (PMF.uniformOfFintype (Fin 256)).map ternaryOfByte = EntryLaw.ternary.rowPMF 4 := by
  let f (b : Fin 256) (i : Fin 4) :=
    (b.val.testBit (2 * i.val), b.val.testBit (2 * i.val + 1))
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 8
    · have hp := congrFun hab (⟨k / 2, by omega⟩ : Fin 4)
      have h0 := congrArg Prod.fst hp
      have h1 := congrArg Prod.snd hp
      dsimp [f] at h0 h1
      rcases Nat.mod_two_eq_zero_or_one k with he | he
      · simpa only [show 2 * (k / 2) = k by omega] using h0
      · simpa only [show 2 * (k / 2) + 1 = k by omega] using h1
    · have hp : 256 ≤ 2 ^ k := by
        calc
          256 = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hp),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hp)]
  let e := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp⟩)
  rw [EntryLaw.rowPMF, uniformPiMap, uniformPiPMF_eq_uniformOfFintype, EntryLaw.ternary,
    ← map_uniformOfFintype_equiv e, PMF.map_comp]
  rfl

/-- The entry of a core of the ring-equation check read from an accepted byte `b < 250`:
`b % 25 - 12`. Spec F §6.3. -/
def uniformOfByte (b : Fin 250) : ℤ := ((b.val % 25 : ℕ) : ℤ) - 12

/-- The entry read from a uniform accepted byte is uniform on the integers from `-12` to `12`. -/
theorem map_uniformOfByte :
    (PMF.uniformOfFintype (Fin 250)).map uniformOfByte = (EntryLaw.uniform 12).entryPMF := by
  change (PMF.uniformOfFintype (Fin 250)).map uniformOfByte =
    (PMF.uniformOfFintype (Fin 25)).map (fun s => (s.val : ℤ) - 12)
  rw [← map_uniformOfFintype_equiv (finProdFinEquiv : Fin 10 × Fin 25 ≃ Fin 250),
    PMF.map_comp, ← Probability.map_uniformOfFintype_prod_snd (Fin 10) (Fin 25),
    PMF.map_comp]
  congr 1
  funext s
  simp [uniformOfByte, finProdFinEquiv, Nat.add_mod,
    Nat.mod_eq_of_lt s.2.isLt]

/-- A uniform byte conditioned on being less than `250` is uniform on the `250` accepted values. -/
theorem filter_byte_lt
    (h : ∃ b ∈ {b : Fin 256 | b.val < 250}, b ∈ (PMF.uniformOfFintype (Fin 256)).support) :
    (PMF.uniformOfFintype (Fin 256)).filter {b | b.val < 250} h =
      (PMF.uniformOfFintype (Fin 250)).map (Fin.castLE (by norm_num)) := by
  classical
  let e : Fin 250 ≃ {b : Fin 256 // b.val < 250} :=
    { toFun := fun b => ⟨Fin.castLE (by norm_num) b, b.isLt⟩
      invFun := fun b => ⟨b.val.val, b.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : (∑' b : Fin 256,
      ({b : Fin 256 | b.val < 250}.indicator (PMF.uniformOfFintype (Fin 256))) b) =
      (250 : ENNReal) * 256⁻¹ := by
    rw [← tsum_subtype]
    change (∑' b : {b : Fin 256 // b.val < 250},
      PMF.uniformOfFintype (Fin 256) b.val) = _
    rw [← e.tsum_eq]
    simp [PMF.uniformOfFintype_apply, tsum_fintype]
  apply PMF.ext
  intro b
  rw [PMF.filter_apply, hs, PMF.map_apply]
  by_cases hb : b.val < 250
  · let a : Fin 250 := ⟨b.val, hb⟩
    have ha : b = Fin.castLE (by norm_num) a := Fin.ext rfl
    rw [tsum_eq_single a]
    · simp only [ha, Set.mem_ofPred_eq, Fin.val_castLE, Fin.is_lt, Set.indicator_of_mem,
        PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat, if_true]
      rw [ENNReal.mul_inv (by simp) (by simp), inv_inv, mul_comm 250⁻¹,
        ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]
    · intro c hc
      have hne : b ≠ Fin.castLE (by norm_num) c := by
        intro he
        apply hc
        apply Fin.ext
        exact (congrArg Fin.val he).symm
      simp [hne]
  · have hne (c : Fin 250) : b ≠ Fin.castLE (by norm_num) c := by
      intro he
      have := congrArg Fin.val he
      have := c.isLt
      simp only [Fin.val_castLE] at *
      omega
    simp [hb, hne]

end CertifiedProjections.Aerie
