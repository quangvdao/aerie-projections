/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Tobias Rothmann
-/

import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Centered modular representatives

This module packages `ZMod.valMinAbs` in the integer notation used by the
paper. For an odd positive modulus, it proves the exact centered-interval
specification, uniqueness, least absolute value, and contraction.
-/

namespace CertifiedProjections

/-- The centered integer representative of `z` modulo `q`. For positive odd
`q`, it lies in `[-(q - 1) / 2, (q - 1) / 2]`. -/
def centeredMod (q : ℕ) (z : ℤ) : ℤ :=
  (z : ZMod q).valMinAbs

/-- The balanced integer interval for an odd modulus `q`. -/
def centeredInterval (q : ℕ) : Set ℤ :=
  Set.Icc (-((q / 2 : ℕ) : ℤ)) ((q / 2 : ℕ) : ℤ)

/-- Centered reduction represents the same residue class. -/
@[simp]
theorem centeredMod_intCast (q : ℕ) (z : ℤ) :
    (centeredMod q z : ZMod q) = z := by
  simp [centeredMod, ZMod.coe_valMinAbs]

/--
For odd `q`, the doubled `ZMod.valMinAbs` range is exactly the paper's
closed centered interval.
-/
theorem two_mul_mem_Ioc_iff_mem_centeredInterval {q : ℕ} (hq : Odd q) (y : ℤ) :
    y * 2 ∈ Set.Ioc (-(q : ℤ)) q ↔ y ∈ centeredInterval q := by
  obtain ⟨k, rfl⟩ := hq
  simp only [centeredInterval, Set.mem_Ioc, Set.mem_Icc]
  norm_num
  omega

/--
The exact existence-and-uniqueness specification for centered reduction.

An integer equals `centeredMod q z` precisely when it represents `z` modulo
`q` and lies in the centered interval.
-/
theorem centeredMod_eq_iff {q : ℕ} (hq : Odd q) (z y : ℤ) :
    centeredMod q z = y ↔
      (y : ZMod q) = z ∧ y ∈ centeredInterval q := by
  have hq0 : q ≠ 0 := by
    obtain ⟨k, rfl⟩ := hq
    omega
  let : NeZero q := ⟨hq0⟩
  rw [centeredMod, ZMod.valMinAbs_spec]
  constructor
  · rintro ⟨hy, hyrange⟩
    exact ⟨hy.symm, (two_mul_mem_Ioc_iff_mem_centeredInterval hq y).mp hyrange⟩
  · rintro ⟨hy, hyrange⟩
    exact ⟨hy.symm, (two_mul_mem_Ioc_iff_mem_centeredInterval hq y).mpr hyrange⟩

/-- Centered reduction lies in the centered interval for every odd modulus. -/
theorem centeredMod_mem_centeredInterval {q : ℕ} (hq : Odd q) (z : ℤ) :
    centeredMod q z ∈ centeredInterval q :=
  (centeredMod_eq_iff hq z (centeredMod q z)).mp rfl |>.2

/-- The centered interval contains at most one representative of each residue. -/
theorem centeredMod_unique {q : ℕ} (hq : Odd q) {z y : ℤ}
    (hy : (y : ZMod q) = z) (hyI : y ∈ centeredInterval q) :
    y = centeredMod q z :=
  ((centeredMod_eq_iff hq z y).mpr ⟨hy, hyI⟩).symm

/--
`ZMod.valMinAbs` has least natural absolute value among all integer
representatives of the same residue.
-/
theorem centeredMod_natAbs_le_of_intCast_eq {q : ℕ} [NeZero q] {z y : ℤ}
    (hy : (y : ZMod q) = z) :
    (centeredMod q z).natAbs ≤ y.natAbs := by
  have hmem := ZMod.valMinAbs_mem_Ioc (z : ZMod q)
  rw [Set.mem_Ioc] at hmem
  have hcast :
      (y : ZMod q) = (((z : ZMod q).valMinAbs : ℤ) : ZMod q) := by
    rw [hy, ZMod.coe_valMinAbs]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  obtain ⟨t, ht⟩ := hcast
  have hq : (1 : ℤ) ≤ (q : ℤ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  rcases eq_or_ne t 0 with rfl | ht0
  · simp only [mul_zero] at ht
    simp only [centeredMod]
    omega
  · have habs : q ≤ ((q : ℤ) * t).natAbs := by
      have ht1 : 1 ≤ t.natAbs := Int.natAbs_pos.mpr ht0
      rw [Int.natAbs_mul]
      simp only [Int.natAbs_natCast]
      nlinarith [ht1]
    revert ht habs
    generalize (q : ℤ) * t = k
    intro ht habs
    simp only [centeredMod]
    omega

/-- Centered reduction cannot increase natural absolute value, for any modulus.
For modulus zero, `ZMod 0` is the integers and centered reduction is the identity. -/
theorem centeredMod_natAbs_le (q : ℕ) (z : ℤ) :
    (centeredMod q z).natAbs ≤ z.natAbs := by
  by_cases hq : q = 0
  · subst q
    rfl
  · let _ : NeZero q := ⟨hq⟩
    exact centeredMod_natAbs_le_of_intCast_eq (q := q) (z := z) (y := z) rfl

/-- Centered reduction cannot increase integer absolute value, for any modulus. -/
theorem abs_centeredMod_le (q : ℕ) (z : ℤ) :
    |centeredMod q z| ≤ |z| := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast centeredMod_natAbs_le q z

/-- Centered reduction fixes integers already in the centered interval. -/
@[simp]
theorem centeredMod_eq_self {q : ℕ} (hq : Odd q) {z : ℤ}
    (hz : z ∈ centeredInterval q) :
    centeredMod q z = z :=
  (centeredMod_eq_iff hq z z).mpr ⟨rfl, hz⟩

/--
The full centered-representative contract used by the paper.

For positive odd modulus, `centeredMod q z` is congruent to `z`, belongs to
the centered interval, has least absolute value among all congruent integers,
has absolute value at most `|z|`, and is the unique congruent integer in that
interval.
-/
theorem centeredMod_spec {q : ℕ} (hq : Odd q) (z : ℤ) :
    ((centeredMod q z : ZMod q) = z) ∧
      centeredMod q z ∈ centeredInterval q ∧
      (∀ y : ℤ, (y : ZMod q) = z →
        |centeredMod q z| ≤ |y|) ∧
      |centeredMod q z| ≤ |z| ∧
      (∀ y : ℤ, (y : ZMod q) = z →
        y ∈ centeredInterval q → y = centeredMod q z) := by
  have hq0 : q ≠ 0 := by
    obtain ⟨k, rfl⟩ := hq
    omega
  let : NeZero q := ⟨hq0⟩
  refine ⟨centeredMod_intCast q z, centeredMod_mem_centeredInterval hq z,
    ?_, abs_centeredMod_le q z, ?_⟩
  · intro y hy
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact_mod_cast centeredMod_natAbs_le_of_intCast_eq hy
  · intro y hy hyI
    exact centeredMod_unique hq hy hyI

end CertifiedProjections
