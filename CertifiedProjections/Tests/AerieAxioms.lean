/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie

/-!
# Multi-stage projections for Aerie: statement and axiom checks

The headline declarations of the Aerie instance exist under their documented names, and every
declaration of the Aerie modules and of the certificates they use depends only on the standard
axioms. This root builds the norm comparison certificate, so it belongs to the kernel validation
group and not to fast validation.
-/

namespace CertifiedProjections.Tests.AerieAxioms

open CertifiedProjections.MultiStage CertifiedProjections.Aerie

#check @falcon512_valid
#check @falcon1024_valid
#check @falcon512_ringCheckError_le
#check @falcon1024_ringCheckError_le
#check @EntryLaw.ternary_mgfConstant
#check @normComparison_exists
#check @normCheck_accept_le
#check @normCheck_reject_le
#check @Aerie.ringCheck_accept_le
#check @Aerie.ringCheck_reject_le
#check @normIdentity_lift
#check @sqNorm_residual_le
#check @projection_sound
#check @exists_residual_eq_mul_of_not_projectionBad
#check @projection_complete
#check @falcon512_honest_le
#check @falcon1024_honest_le
#check @falcon512Geometry_fanInLe
#check @falcon1024Geometry_fanInLe
#check @normCheck_eq_map_normProjection
#check @ringCheck_eq_map_ringProjection
#check @projectionCheck_eq_map
#check @map_ternaryOfByte
#check @map_uniformOfByte
#check @filter_byte_lt
#check @FalconWitness
#check @falconWitness_of_not_projectionBad
#check @projection_sound_of_not_falconWitness
#check @projection_complete_of_falconWitness
#check @Geometry.projectionCheck_eq_map_outputs
#check @falcon512_projection_sound
#check @falcon1024_projection_sound
#check @falcon512_projection_complete
#check @falcon1024_projection_complete

example : eta = 2 ^ 15 := rfl

open Lean in
run_cmd
  let env ← getEnv
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : Array Name := #[`CertifiedProjections.Aerie,
    `CertifiedProjections.Certificates.Families.Aerie,
    `CertifiedProjections.Certificates.Families.MultiStage]
  let mut count := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let module := env.header.moduleNames[idx.toNat]!
    unless prefixes.any (·.isPrefixOf module) do continue
    count := count + 1
    if info matches .axiomInfo _ then throwError "{name} is an axiom"
    for ax in ← collectAxioms name do
      unless standard.contains ax do throwError "{name} depends on the axiom {ax}"
  if count < 200 then throwError "only {count} declarations found in the Aerie modules"

end CertifiedProjections.Tests.AerieAxioms
