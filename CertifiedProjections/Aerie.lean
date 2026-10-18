/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.Cores
import CertifiedProjections.Aerie.Falcon
import CertifiedProjections.Aerie.Geometry
import CertifiedProjections.Aerie.Lift
import CertifiedProjections.Aerie.Main
import CertifiedProjections.Aerie.NormCheck
import CertifiedProjections.Aerie.Params
import CertifiedProjections.Aerie.RingCheck
import CertifiedProjections.Aerie.Sampling

/-!
# Multi-stage projections for Aerie

This opt-in umbrella exposes the Aerie instance of `CertifiedProjections.MultiStage`: the parameter
sets, the norm check, the ring check, the lift to Falcon witnesses, the main soundness theorem, the
table shapes of the protocol, the seeds of the cores, the byte sampling maps, and the soundness and
completeness theorems for Falcon-512 and Falcon-1024 (`Aerie/Falcon.lean`). Spec references are to
`specs/falcon-projection-theorem.md` in `a16z/aerie`, and those marked `F` to `specs/falcon.md`.

The spec uses other words for some of these objects. It calls a branch of the norm check a group,
the cores of the branch stages prefix cores, the core of the final stage the terminal core, the
norm check the norm leg, and the ring-equation check the residual leg.
-/
