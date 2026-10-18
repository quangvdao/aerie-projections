/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.Geometry

/-!
# Constants of the Aerie specification

Every example states that a definition of the Aerie instance equals the value of the same constant
in the Aerie specification. The file is generated in the Aerie repository by
`specs/scripts/falcon_projection_lean.py` from `specs/scripts/falcon_projection_certificate.json`,
and that repository records the SHA-256 of this file. Do not edit it by hand.
-/

namespace CertifiedProjections.Tests.AerieSpecConstants

open CertifiedProjections.MultiStage CertifiedProjections.Aerie

/-! ## Constants shared by both parameter sets -/

example : branchRows = 43 := rfl
example : numBranchStages = 4 := rfl
example : numBranches = 4 := rfl
example : finalRows = 156 := rfl
example : normCheckError = 2⁻¹ ^ 136 := rfl

/-! ## Falcon-512 -/

example : falcon512.p = 18446744073709551557 := by decide
example : falcon512.q = 12289 := rfl
example : falcon512.n = 512 := rfl
example : falcon512.betaSq = 34034726 := rfl
example : falcon512.maxSignatures = 65536 := by decide
example : falcon512.acceptSqNorm = 5092300183991442303232 := rfl
example : falcon512.fanInMax = ![4096, 688, 688, 688, 688] := rfl
example : falcon512.s2Bound = 2047 := rfl
example : falcon512.publicBound = 6144 := rfl
example : falcon512.residualEntryBound = 811061395 := rfl
example : falcon512.ringEntryBound = 12 := rfl
example : falcon512.ringRows = ![31, 31, 31] := rfl
example : falcon512.overflowOrder = 136 := rfl
example : falcon512.honestOrder = 46 := rfl
example : eta = 32768 := by norm_num [eta]
example : falcon512.soundSqNorm = 5092300183991442303233 / 32768 := by
  norm_num [Params.soundSqNorm, falcon512, eta]
example : falcon512.honestSqNorm = 2230499803136 := by decide
example : falcon512.residualSqNorm = 22072796136550246960332800 := by decide
example : Nat.sqrt falcon512.betaSq = 5833 := by
  symm; rw [Nat.eq_sqrt]; decide
/-- The integer square root of the acceptance bound of Falcon-512. -/
theorem falcon512_sqrtAcceptSqNorm : falcon512.sqrtAcceptSqNorm = 71360354427 := by
  unfold Params.sqrtAcceptSqNorm; symm; rw [Nat.eq_sqrt]; decide
example : falcon512.tau 0 = 4567062683360 := by
  rw [Params.tau, falcon512_sqrtAcceptSqNorm]; decide
example : falcon512.tau 1 = 2283531341680 := by
  rw [Params.tau, falcon512_sqrtAcceptSqNorm]; decide
example : falcon512.tau 2 = 1141765670840 := by
  rw [Params.tau, falcon512_sqrtAcceptSqNorm]; decide
example : falcon512.tau 3 = 570882835420 := by
  rw [Params.tau, falcon512_sqrtAcceptSqNorm]; decide
example : falcon512.tau 4 = 285441417710 := by
  rw [Params.tau, falcon512_sqrtAcceptSqNorm]; decide
example : falcon512.tau 5 = 142720708855 := by
  rw [Params.tau, falcon512_sqrtAcceptSqNorm]; decide
example : (falcon512Geometry 14).numRecords = 65536 := by decide
example : (falcon512Geometry 14).normRadices falcon512.n = ![4096, 16, 16, 16, 4] := by
  decide
example : (falcon512Geometry 14).ringRadices falcon512.n = ![2048, 128, 128] := by
  decide
example : ((falcon512Geometry 14).normShape falcon512.n).f = ![4096, 688, 688, 688, 688] := by
  decide

/-! ## Falcon-1024 -/

example : falcon1024.p = 18446744073709551557 := by decide
example : falcon1024.q = 12289 := rfl
example : falcon1024.n = 1024 := rfl
example : falcon1024.betaSq = 70265242 := rfl
example : falcon1024.maxSignatures = 65536 := by decide
example : falcon1024.acceptSqNorm = 10513136047130310946696 := rfl
example : falcon1024.fanInMax = ![4096, 688, 688, 688, 1376] := rfl
example : falcon1024.s2Bound = 2047 := rfl
example : falcon1024.publicBound = 6144 := rfl
example : falcon1024.residualEntryBound = 1648068606 := rfl
example : falcon1024.ringEntryBound = 12 := rfl
example : falcon1024.ringRows = ![31, 31, 31] := rfl
example : falcon1024.overflowOrder = 60 := rfl
example : falcon1024.honestOrder = 46 := rfl
example : eta = 32768 := by norm_num [eta]
example : falcon1024.soundSqNorm = 10513136047130310946697 / 32768 := by
  norm_num [Params.soundSqNorm, falcon1024, eta]
example : falcon1024.honestSqNorm = 4604902899712 := by decide
example : falcon1024.residualSqNorm = 182276407506027808926203904 := by decide
example : Nat.sqrt falcon1024.betaSq = 8382 := by
  symm; rw [Nat.eq_sqrt]; decide
/-- The integer square root of the acceptance bound of Falcon-1024. -/
theorem falcon1024_sqrtAcceptSqNorm : falcon1024.sqrtAcceptSqNorm = 102533584971 := by
  unfold Params.sqrtAcceptSqNorm; symm; rw [Nat.eq_sqrt]; decide
example : falcon1024.tau 0 = 6562149438176 := by
  rw [Params.tau, falcon1024_sqrtAcceptSqNorm]; decide
example : falcon1024.tau 1 = 3281074719088 := by
  rw [Params.tau, falcon1024_sqrtAcceptSqNorm]; decide
example : falcon1024.tau 2 = 1640537359544 := by
  rw [Params.tau, falcon1024_sqrtAcceptSqNorm]; decide
example : falcon1024.tau 3 = 820268679772 := by
  rw [Params.tau, falcon1024_sqrtAcceptSqNorm]; decide
example : falcon1024.tau 4 = 410134339886 := by
  rw [Params.tau, falcon1024_sqrtAcceptSqNorm]; decide
example : falcon1024.tau 5 = 205067169943 := by
  rw [Params.tau, falcon1024_sqrtAcceptSqNorm]; decide
example : (falcon1024Geometry 15).numRecords = 65536 := by decide
example : (falcon1024Geometry 15).normRadices falcon1024.n = ![4096, 16, 16, 16, 8] := by
  decide
example : (falcon1024Geometry 15).ringRadices falcon1024.n = ![2048, 128, 256] := by
  decide
example : ((falcon1024Geometry 15).normShape falcon1024.n).f = ![4096, 688, 688, 688, 1376] := by
  decide

end CertifiedProjections.Tests.AerieSpecConstants
