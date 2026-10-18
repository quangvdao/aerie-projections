/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.Main
import CertifiedProjections.MultiStage.Flat

/-!
# Table shapes of the Aerie projections

The shapes and re-indexings of the two checks as the protocol fixes them (spec F §6.1–6.3). Every
re-indexing is `flatEquiv`: it preserves the flat index of an entry.

`NormShape.ofRadices` and `RingShape.ofRadices` build the shapes from a list of radices. A
`Geometry` holds the number `splitBits` of low bits of the record index that the first stage
contracts (`b_split`) and the number `highBits` of remaining bits (`R`). It determines the number of
records `Geometry.numRecords`, the radices `Geometry.normRadices` and `Geometry.ringRadices` (spec F
(6.6)), the shapes, and the placements `Geometry.normPlacement` and `Geometry.ringPlacement` of the
two sources in the input tables. `Geometry.projectionCheck` is `projectionCheck` for these.

For the two parameter sets, `falcon512Geometry R` and `falcon1024Geometry R` are the geometries of
the spec, for which `normRadices 0 = 2 ^ 12` and `ringRadices 0 = 2 ^ 11`.
-/

namespace CertifiedProjections.Aerie

open MultiStage

/-- The shape of the norm check for the radices `r`. The input table has `r 0` rows, and its column
index has the four digits `x₁, …, x₄` with radices `r 1, …, r 4`, least significant first. Branch
stage `i ≥ 1` contracts the `branchRows` rows of the previous output with the digit `xᵢ`, in the
row `k + branchRows * xᵢ`; the final stage contracts the `numBranches * branchRows` stacked rows
with `x₄`. The spec writes `r_1, …, r_5` for `r 0, …, r 4`, `x_1` for the row index of the input and
`x_2, …, x_5` for `x₁, …, x₄`. Spec F §6.3. -/
def NormShape.ofRadices (r : Fin 5 → ℕ) : NormShape where
  f := ![r 0, r 1 * branchRows, r 2 * branchRows, r 3 * branchRows,
    r 4 * (numBranches * branchRows)]
  F := ![r 4 * r 3 * r 2 * r 1, r 4 * r 3 * r 2, r 4 * r 3, r 4, 1]
  e₁ := flatEquiv (Nat.mul_assoc _ _ _)
  e₂ := flatEquiv (Nat.mul_assoc _ _ _)
  e₃ := flatEquiv (Nat.mul_assoc _ _ _)
  e₄ := flatEquiv (Nat.one_mul _).symm

/-- The shape of the ring-equation check for the radices `r`. The input table has `r 0` rows, and
its column index has the two digits `x₁, x₂` with radices `r 1, r 2`, least significant first. Stage
`i ≥ 1` contracts the rows of the previous output with the digit `xᵢ`. The spec writes
`r'_1, r'_2, r'_3` for `r 0, r 1, r 2`, `x_1` for the row index of the input and `x_2, x_3` for
`x₁, x₂`. Spec F §6.3. -/
def RingShape.ofRadices (rows : Fin 3 → ℕ) (r : Fin 3 → ℕ) : RingShape rows where
  f := ![r 0, r 1 * rows 0, r 2 * rows 1]
  F := ![r 2 * r 1, r 2, 1]
  e₁ := flatEquiv (Nat.mul_assoc _ _ _)
  e₂ := flatEquiv (Nat.one_mul _).symm

/-- The split of the record index. The first stage of each check contracts the coefficient index
together with the low `splitBits` bits of the record index (`b_split`); the later stages contract
the remaining `highBits` bits (`R`). Spec F (6.6). -/
structure Geometry where
  /-- `b_split`: the number of low bits of the record index contracted by the first stage. -/
  splitBits : ℕ
  /-- `R`: the number of remaining bits of the record index. -/
  highBits : ℕ

namespace Geometry

/-- The number of records `2 ^ (splitBits + highBits)`, counting padding records (`N*`). -/
def numRecords (G : Geometry) : ℕ := 2 ^ (G.splitBits + G.highBits)

/-- The radices of the norm check for ring degree `n`. The first is `2 ^ splitBits * (2 * n)`. Each
of the next three takes `min 4` of the bits that remain, and the last takes the rest. Spec F
§6.2. -/
def normRadices (G : Geometry) (n : ℕ) : Fin 5 → ℕ :=
  ![2 ^ G.splitBits * (2 * n), 2 ^ min 4 G.highBits, 2 ^ min 4 (G.highBits - 4),
    2 ^ min 4 (G.highBits - 8), 2 ^ (G.highBits - 12)]

/-- The radices of the ring-equation check for ring degree `n`. The first is `2 ^ splitBits * n`,
the second takes `highBits / 2` bits rounded down, and the third takes the rest. Spec F §6.2. -/
def ringRadices (G : Geometry) (n : ℕ) : Fin 3 → ℕ :=
  ![2 ^ G.splitBits * n, 2 ^ (G.highBits / 2), 2 ^ ((G.highBits + 1) / 2)]

/-- The shape of the norm check for ring degree `n`. -/
def normShape (G : Geometry) (n : ℕ) : NormShape := NormShape.ofRadices (G.normRadices n)

/-- The shape of the ring-equation check for the parameters `P`. -/
def ringShape (G : Geometry) (P : Params) : RingShape P.ringRows :=
  RingShape.ofRadices P.ringRows (G.ringRadices P.n)

/-- The input table of the norm check has as many entries as the norm source. -/
theorem normShape_card (G : Geometry) (n : ℕ) :
    G.numRecords * (2 * n) = (G.normShape n).F 0 * (G.normShape n).f 0 := by
  change 2 ^ (G.splitBits + G.highBits) * (2 * n) =
    (2 ^ (G.highBits - 12) * 2 ^ min 4 (G.highBits - 8) *
      2 ^ min 4 (G.highBits - 4) * 2 ^ min 4 G.highBits) *
        (2 ^ G.splitBits * (2 * n))
  have h : G.highBits - 12 + min 4 (G.highBits - 8) +
      min 4 (G.highBits - 4) + min 4 G.highBits = G.highBits := by omega
  rw [← pow_add, ← pow_add, ← pow_add, h]
  rw [← mul_assoc (2 ^ G.highBits) (2 ^ G.splitBits), ← pow_add,
    Nat.add_comm G.highBits]

/-- The input table of the ring-equation check has as many entries as the residual. -/
theorem ringShape_card (G : Geometry) (P : Params) :
    G.numRecords * P.n = (G.ringShape P).F 0 * (G.ringShape P).f 0 := by
  change 2 ^ (G.splitBits + G.highBits) * P.n =
    (2 ^ ((G.highBits + 1) / 2) * 2 ^ (G.highBits / 2)) * (2 ^ G.splitBits * P.n)
  have h : (G.highBits + 1) / 2 + G.highBits / 2 = G.highBits := by omega
  rw [← pow_add, h, ← mul_assoc, ← pow_add, Nat.add_comm G.highBits]

/-- The placement of the norm source in the input table of the norm check: the entry in row `j` of
record `i` has flat index `j + 2 * n * i`. Spec F (6.1). -/
def normPlacement (G : Geometry) (n : ℕ) :
    Fin (2 * n) × Fin G.numRecords ≃ Fin ((G.normShape n).f 0) × Fin ((G.normShape n).F 0) :=
  flatEquiv (G.normShape_card n)

/-- The placement of the residual in the input table of the ring-equation check: coefficient `j` of
record `i` has flat index `j + n * i`. Spec F (6.2). -/
def ringPlacement (G : Geometry) (P : Params) :
    Fin P.n × Fin G.numRecords ≃ Fin ((G.ringShape P).f 0) × Fin ((G.ringShape P).F 0) :=
  flatEquiv (G.ringShape_card P)

/-- The two checks of the protocol for the geometry `G`: `projectionCheck` on the norm table of
`src` and on the residual of `src`, placed by flat index. Spec F (6.3). -/
noncomputable def projectionCheck (G : Geometry) (P : Params)
    (pub : PublicInput P.n G.numRecords) (src : Source P.n G.numRecords) :
    PMF (Table finalRows ((G.normShape P.n).F 4) × Table (P.ringRows 2) ((G.ringShape P).F 2)) :=
  Aerie.projectionCheck P (G.normShape P.n) (G.ringShape P)
    (reshape (G.normPlacement P.n) src.normTable)
    (reshape (G.ringPlacement P) (residual pub src))

end Geometry

/-- The geometry of Falcon-512 with `2 ^ (2 + R)` records: `b_split = 12 - (9 + 1) = 2`. Spec F
(6.6). -/
def falcon512Geometry (R : ℕ) : Geometry := ⟨2, R⟩

/-- The geometry of Falcon-1024 with `2 ^ (1 + R)` records: `b_split = 12 - (10 + 1) = 1`. Spec F
(6.6). -/
def falcon1024Geometry (R : ℕ) : Geometry := ⟨1, R⟩

/-- For Falcon-512 the first radix of the norm check is `2 ^ 12` and that of the ring-equation
check is `2 ^ 11`. Spec F §6.2. -/
theorem falcon512Geometry_radices_zero (R : ℕ) :
    (falcon512Geometry R).normRadices falcon512.n 0 = 2 ^ 12 ∧
      (falcon512Geometry R).ringRadices falcon512.n 0 = 2 ^ 11 := by
  norm_num [falcon512Geometry, Geometry.normRadices, Geometry.ringRadices, falcon512]

/-- For Falcon-1024 the first radix of the norm check is `2 ^ 12` and that of the ring-equation
check is `2 ^ 11`. Spec F §6.2. -/
theorem falcon1024Geometry_radices_zero (R : ℕ) :
    (falcon1024Geometry R).normRadices falcon1024.n 0 = 2 ^ 12 ∧
      (falcon1024Geometry R).ringRadices falcon1024.n 0 = 2 ^ 11 := by
  norm_num [falcon1024Geometry, Geometry.normRadices, Geometry.ringRadices, falcon1024]

/-- For Falcon-512 with at most `2 ^ 16` records (`R ≤ 14`), every fan-in of the norm check is at
most the bound in the parameters. -/
theorem falcon512Geometry_fanInLe {R : ℕ} (hR : R ≤ 14) :
    ((falcon512Geometry R).normShape falcon512.n).FanInLe falcon512 := by
  intro i
  fin_cases i
  · norm_num [Geometry.normShape, NormShape.ofRadices, Geometry.normRadices,
      falcon512Geometry, falcon512]
  · change 2 ^ min 4 R * 43 ≤ 2 ^ 4 * 43
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
  · change 2 ^ min 4 (R - 4) * 43 ≤ 2 ^ 4 * 43
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
  · change 2 ^ min 4 (R - 8) * 43 ≤ 2 ^ 4 * 43
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
  · change 2 ^ (R - 12) * (4 * 43) ≤ 2 ^ 2 * (4 * 43)
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))

/-- For Falcon-1024 with at most `2 ^ 16` records (`R ≤ 15`), every fan-in of the norm check is at
most the bound in the parameters. -/
theorem falcon1024Geometry_fanInLe {R : ℕ} (hR : R ≤ 15) :
    ((falcon1024Geometry R).normShape falcon1024.n).FanInLe falcon1024 := by
  intro i
  fin_cases i
  · norm_num [Geometry.normShape, NormShape.ofRadices, Geometry.normRadices,
      falcon1024Geometry, falcon1024]
  · change 2 ^ min 4 R * 43 ≤ 2 ^ 4 * 43
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
  · change 2 ^ min 4 (R - 4) * 43 ≤ 2 ^ 4 * 43
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
  · change 2 ^ min 4 (R - 8) * 43 ≤ 2 ^ 4 * 43
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
  · change 2 ^ (R - 12) * (4 * 43) ≤ 2 ^ 3 * (4 * 43)
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))

/-- For Falcon-512 with `R ≤ 14` the number of records is at most `falcon512.maxSignatures`. -/
theorem falcon512Geometry_numRecords_le {R : ℕ} (hR : R ≤ 14) :
    (falcon512Geometry R).numRecords ≤ falcon512.maxSignatures := by
  change 2 ^ (2 + R) ≤ 2 ^ 16
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- For Falcon-1024 with `R ≤ 15` the number of records is at most `falcon1024.maxSignatures`. -/
theorem falcon1024Geometry_numRecords_le {R : ℕ} (hR : R ≤ 15) :
    (falcon1024Geometry R).numRecords ≤ falcon1024.maxSignatures := by
  change 2 ^ (1 + R) ≤ 2 ^ 16
  exact Nat.pow_le_pow_right (by decide) (by omega)

end CertifiedProjections.Aerie
