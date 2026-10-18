/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.Main

/-!
# The two checks as functions of the cores

A core is the random matrix of one stage. Each entry of a core is the value of a seed of the entry
law, and `CoreSeeds μ c f` is the type of the seeds of a core with `c` rows and `f` columns.
`core s` is the matrix of the seeds `s`. By `stage_eq_map_core`, a stage multiplies its input by the
core of uniform seeds. These seeds are not the transcript seed of spec F §6.3, from which the
protocol derives all cores.

`NormCoreSeeds sh` collects the seeds of the cores of the norm check: four per branch and one for
the final stage. `normProjection sh s S` is the output of the norm check on `S` over the integers
as a function of the seeds `s`. `normCheck_eq_map_normProjection` says that the law
`normCheck p sh S` is the law of `ctr p (normProjection sh s S)` for uniform seeds `s`.
`RingCoreSeeds`, `ringProjection` and `ringCheck_eq_map_ringProjection` are the same for the
ring-equation check, and `projectionCheck_eq_map` combines the two.

Uniform seeds of the product type make all cores independent, with independent entries of the
stated law. This is spec hypothesis H1, and these theorems identify the probability space of
`projection_sound` with the choice of the cores.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.MultiStage

variable {c f F : ℕ}

/-- The seeds of a core with `c` rows and `f` columns: one seed of the entry law `μ` per entry. -/
abbrev CoreSeeds (μ : EntryLaw) (c f : ℕ) : Type := Fin c → Fin f → μ.Seed

/-- The core of the seeds `s`: the matrix whose entry `(i, j)` is the value of the seed `s i j`. -/
def core {μ : EntryLaw} (s : CoreSeeds μ c f) : Matrix (Fin c) (Fin f) ℤ :=
  Matrix.of fun i j => μ.value (s i j)

/-- A stage multiplies its input by the core of uniform seeds. -/
theorem stage_eq_map_core (μ : EntryLaw) (c : ℕ) (X : Table f F) :
    stage μ c X = (PMF.uniformOfFintype (CoreSeeds μ c f)).map fun s => core s * X := by
  simp only [stage, EntryLaw.matrixPMF, uniformPiMap,
    uniformPiPMF_eq_uniformOfFintype, PMF.map_comp]
  rfl

end CertifiedProjections.MultiStage

namespace CertifiedProjections.Aerie

open MultiStage

/-- Sampling two uniform seeds in sequence is uniform sampling of their pair. -/
private theorem uniform_bind_map {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (g : α → β → γ) :
    (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (g a)) =
      (PMF.uniformOfFintype (α × β)).map (fun x => g x.1 x.2) := by
  rw [Probability.uniformOfFintype_prod_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

/-- Independent uniform coordinates form a uniform function. -/
private theorem piPMF_uniform (α : Type*) [Fintype α] [Nonempty α] (g : ℕ) :
    piPMF (fun _ : Fin g => PMF.uniformOfFintype α) =
      PMF.uniformOfFintype (Fin g → α) := by
  apply PMF.ext
  intro x
  simp [piPMF_apply, PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- The seeds of the four cores of one branch of the norm check. Spec F §6.3. -/
def NormBranchCoreSeeds (sh : NormShape) : Type :=
  CoreSeeds EntryLaw.ternary branchRows (sh.f 0) × CoreSeeds EntryLaw.ternary branchRows (sh.f 1) ×
    CoreSeeds EntryLaw.ternary branchRows (sh.f 2) × CoreSeeds EntryLaw.ternary branchRows (sh.f 3)

instance NormBranchCoreSeeds.instFintype (sh : NormShape) : Fintype (NormBranchCoreSeeds sh) := by
  unfold NormBranchCoreSeeds; infer_instance

instance NormBranchCoreSeeds.instNonempty (sh : NormShape) : Nonempty (NormBranchCoreSeeds sh) := by
  unfold NormBranchCoreSeeds; infer_instance

/-- The seeds of all cores of the norm check: those of the `numBranches` branches and that of the
final stage. Spec F §6.3. -/
def NormCoreSeeds (sh : NormShape) : Type :=
  (Fin numBranches → NormBranchCoreSeeds sh) × CoreSeeds EntryLaw.ternary finalRows (sh.f 4)

instance NormCoreSeeds.instFintype (sh : NormShape) : Fintype (NormCoreSeeds sh) := by
  unfold NormCoreSeeds; infer_instance

instance NormCoreSeeds.instNonempty (sh : NormShape) : Nonempty (NormCoreSeeds sh) := by
  unfold NormCoreSeeds; infer_instance

/-- The output of one branch of the norm check on `S` over the integers, for the seeds `s`: the four
cores are applied in turn, with the re-indexings `sh.e₁`, `sh.e₂` and `sh.e₃` between them. Spec F
§6.3. -/
def normBranchProjection (sh : NormShape) (s : NormBranchCoreSeeds sh)
    (S : Table (sh.f 0) (sh.F 0)) : Table branchRows (sh.F 3) :=
  core s.2.2.2 * reshape sh.e₃ (core s.2.2.1 * reshape sh.e₂ (core s.2.1 *
    reshape sh.e₁ (core s.1 * S)))

/-- The output of the norm check on `S` over the integers, for the seeds `s`: the outputs of the
branches are stacked, re-indexed by `sh.e₄` and multiplied by the core of the final stage. Spec F
§6.3. -/
def normProjection (sh : NormShape) (s : NormCoreSeeds sh) (S : Table (sh.f 0) (sh.F 0)) :
    Table finalRows (sh.F 4) :=
  core s.2 * reshape sh.e₄ (stack fun g => normBranchProjection sh (s.1 g) S)

/-- One integer norm branch is the image of its uniform tuple of core seeds. -/
private theorem normBranchInt_eq_map (sh : NormShape) (S : Table (sh.f 0) (sh.F 0)) :
    normBranchInt sh S =
      (PMF.uniformOfFintype (NormBranchCoreSeeds sh)).map
        (fun s => normBranchProjection sh s S) := by
  unfold normBranchInt TableKernel.andThen TableKernel.ofFun
  simp only [PMF.bind_bind, PMF.pure_bind]
  simp_rw [stage_eq_map_core, PMF.bind_map, Function.comp_def]
  simp_rw [uniform_bind_map]
  rfl

/-- The law `normCheckInt sh S` is the law of `normProjection sh s S` for uniform seeds `s`. -/
theorem normCheckInt_eq_map_normProjection (sh : NormShape) (S : Table (sh.f 0) (sh.F 0)) :
    normCheckInt sh S =
      (PMF.uniformOfFintype (NormCoreSeeds sh)).map fun s => normProjection sh s S := by
  unfold normCheckInt TableKernel.andThen TableKernel.ofFun branches
  simp only [PMF.bind_bind, PMF.pure_bind]
  simp_rw [normBranchInt_eq_map]
  rw [← piPMF_map, piPMF_uniform]
  simp only [PMF.bind_map]
  simp_rw [stage_eq_map_core, Function.comp_def]
  rw [uniform_bind_map]
  rfl

/-- The law `normCheck p sh S` is the law of `normProjection sh s S` centered modulo `p`, for a
uniform seeds `s`. Spec H1. -/
theorem normCheck_eq_map_normProjection (p : ℕ) (sh : NormShape) (S : Table (sh.f 0) (sh.F 0)) :
    normCheck p sh S =
      (PMF.uniformOfFintype (NormCoreSeeds sh)).map fun s =>
        MultiStage.ctr p (normProjection sh s S) := by
  have hb : normBranch p sh S = normBranch p sh (MultiStage.ctr p S) := by
    unfold normBranch TableKernel.andThen
    rw [stageMod_congr (show MultiStage.ctr p S =
      MultiStage.ctr p (MultiStage.ctr p S) from ctr_ctr.symm)]
  have hc : normCheck p sh S = normCheck p sh (MultiStage.ctr p S) := by
    simp only [normCheck, TableKernel.andThen, branches, hb]
  rw [hc, normCheck_modOf p sh S, normCheckInt_eq_map_normProjection, PMF.map_comp]
  rfl

/-- The seeds of the three cores of the ring-equation check. Spec F §6.3. -/
def RingCoreSeeds (P : Params) (sh : RingShape P.ringRows) : Type :=
  CoreSeeds (EntryLaw.uniform P.ringEntryBound) (P.ringRows 0) (sh.f 0) ×
    CoreSeeds (EntryLaw.uniform P.ringEntryBound) (P.ringRows 1) (sh.f 1) ×
    CoreSeeds (EntryLaw.uniform P.ringEntryBound) (P.ringRows 2) (sh.f 2)

instance RingCoreSeeds.instFintype (P : Params) (sh : RingShape P.ringRows) :
    Fintype (RingCoreSeeds P sh) := by
  unfold RingCoreSeeds; infer_instance

instance RingCoreSeeds.instNonempty (P : Params) (sh : RingShape P.ringRows) :
    Nonempty (RingCoreSeeds P sh) := by
  unfold RingCoreSeeds; infer_instance

/-- The output of the ring-equation check on `Δ` over the integers, for the seeds `s`: the three
cores are applied in turn, with the re-indexings `sh.e₁` and `sh.e₂` between them. Spec F §6.3. -/
def ringProjection (P : Params) (sh : RingShape P.ringRows) (s : RingCoreSeeds P sh)
    (Δ : Table (sh.f 0) (sh.F 0)) : Table (P.ringRows 2) (sh.F 2) :=
  core s.2.2 * reshape sh.e₂ (core s.2.1 * reshape sh.e₁ (core s.1 * Δ))

/-- The law `ringCheckInt P sh Δ` is the law of `ringProjection P sh s Δ` for uniform seeds `s`. -/
theorem ringCheckInt_eq_map_ringProjection (P : Params) (sh : RingShape P.ringRows)
    (Δ : Table (sh.f 0) (sh.F 0)) :
    ringCheckInt P sh Δ =
      (PMF.uniformOfFintype (RingCoreSeeds P sh)).map fun s => ringProjection P sh s Δ := by
  unfold ringCheckInt TableKernel.andThen TableKernel.ofFun
  simp only [PMF.bind_bind, PMF.pure_bind]
  simp_rw [stage_eq_map_core, PMF.bind_map, Function.comp_def]
  simp_rw [uniform_bind_map]
  rfl

/-- The law `ringCheck P sh Δ` is the law of `ringProjection P sh s Δ` centered modulo `P.p`, for a
uniform seeds `s`. Spec H1. -/
theorem ringCheck_eq_map_ringProjection (P : Params) (sh : RingShape P.ringRows)
    (Δ : Table (sh.f 0) (sh.F 0)) :
    ringCheck P sh Δ =
      (PMF.uniformOfFintype (RingCoreSeeds P sh)).map fun s =>
        MultiStage.ctr P.p (ringProjection P sh s Δ) := by
  have hc : ringCheck P sh Δ = ringCheck P sh (MultiStage.ctr P.p Δ) := by
    unfold ringCheck TableKernel.andThen
    rw [stageMod_congr (show MultiStage.ctr P.p Δ =
      MultiStage.ctr P.p (MultiStage.ctr P.p Δ) from ctr_ctr.symm)]
  rw [hc, ringCheck_modOf P sh Δ, ringCheckInt_eq_map_ringProjection, PMF.map_comp]
  rfl

/-- The law `projectionCheck P nsh rsh S Δ` is the law of the pair of the two projections, centered
modulo `P.p`, for uniform seeds of all cores of both checks. Spec H1 and Theorem 6.1. -/
theorem projectionCheck_eq_map (P : Params) (nsh : NormShape) (rsh : RingShape P.ringRows)
    (S : Table (nsh.f 0) (nsh.F 0)) (Δ : Table (rsh.f 0) (rsh.F 0)) :
    projectionCheck P nsh rsh S Δ =
      (PMF.uniformOfFintype (NormCoreSeeds nsh × RingCoreSeeds P rsh)).map fun s =>
        (MultiStage.ctr P.p (normProjection nsh s.1 S),
          MultiStage.ctr P.p (ringProjection P rsh s.2 Δ)) := by
  simp only [projectionCheck, normCheck_eq_map_normProjection,
    ringCheck_eq_map_ringProjection, PMF.bind_map, PMF.map_comp, Function.comp_def]
  exact uniform_bind_map _

end CertifiedProjections.Aerie
