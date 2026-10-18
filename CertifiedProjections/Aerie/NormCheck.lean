/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Certificates.Families.Aerie.NormComparison
import CertifiedProjections.MultiStage.Branch
import CertifiedProjections.MultiStage.Lemmas.Collapse
import CertifiedProjections.MultiStage.Lemmas.NoOverflow
import CertifiedProjections.Certificates.Families.MultiStage.CosineSup

/-!
# Aerie norm check

The norm check `normCheck` consists of four independent branches of four ternary stages each,
stacked and followed by one ternary final stage (spec §3 and Theorem 3.1). A `NormShape` gives the
table shapes and the re-indexings, `normBranch` is one branch, `normBranchInt` and `normCheckInt`
are the same kernels over the integers (`normCheck_modOf`), and `NormAccept` is the acceptance
predicate.

The main results concern a source whose centered squared norm is at least `P.soundSqNorm`.
`normCheck_accept_le_comparison` bounds its acceptance probability by `(1 / 2) ^ finalRows` plus
`ComparisonData.failProb`, and `normCheck_accept_le` bounds it by `normCheckError`.

A stage collapses its input when it maps a table that is large at one threshold to a table that is
small at the next threshold. In the proof, each branch is run over the integers together with a
Boolean that is `true` when some stage of the branch has collapsed its input. The structure
`BranchInvariant` states what is known about this pair after each stage.
-/

open scoped BigOperators ENNReal NNReal

namespace CertifiedProjections.Aerie

open MultiStage

variable {F : ℕ}

/-- Table shapes and re-indexings of the norm check. Spec (3.1)–(3.2). -/
structure NormShape where
  /-- `f i` is the fan-in (the number of rows of the input table) of branch stage `i` for `i ≤ 3`,
  and `f 4` is the fan-in of the final stage. -/
  f : Fin 5 → ℕ
  /-- `F i` is the number of columns of the input table of branch stage `i` for `i ≤ 3`, and `F 4`
  that of the final stage. -/
  F : Fin 5 → ℕ
  /-- The re-indexing of the output of branch stage `0` as the input of branch stage `1`. -/
  e₁ : Fin branchRows × Fin (F 0) ≃ Fin (f 1) × Fin (F 1)
  /-- The re-indexing of the output of branch stage `1` as the input of branch stage `2`. -/
  e₂ : Fin branchRows × Fin (F 1) ≃ Fin (f 2) × Fin (F 2)
  /-- The re-indexing of the output of branch stage `2` as the input of branch stage `3`. -/
  e₃ : Fin branchRows × Fin (F 2) ≃ Fin (f 3) × Fin (F 3)
  /-- The re-indexing of the stacked outputs of the `numBranches` branches as the input of the final
  stage. -/
  e₄ : Fin (numBranches * branchRows) × Fin (F 3) ≃ Fin (f 4) × Fin (F 4)

/-- Every fan-in `sh.f i` is at most the bound `P.fanInMax i` in the parameters. Spec §3.1. -/
def NormShape.FanInLe (sh : NormShape) (P : Params) : Prop :=
  ∀ i, sh.f i ≤ P.fanInMax i

/-- One branch of the norm check modulo `p`: four ternary stages with `branchRows` rows, each
centered modulo `p`, with the re-indexings `sh.e₁`, `sh.e₂` and `sh.e₃` between them. Spec (3.1). -/
noncomputable def normBranch (p : ℕ) (sh : NormShape) :
    TableKernel (sh.f 0) (sh.F 0) branchRows (sh.F 3) :=
  (stageMod p EntryLaw.ternary branchRows).andThen
    (TableKernel.ofFun (reshape sh.e₁)) |>.andThen
    (stageMod p EntryLaw.ternary branchRows) |>.andThen
    (TableKernel.ofFun (reshape sh.e₂)) |>.andThen
    (stageMod p EntryLaw.ternary branchRows) |>.andThen
    (TableKernel.ofFun (reshape sh.e₃)) |>.andThen
    (stageMod p EntryLaw.ternary branchRows)

/-- One branch of the norm check over the integers: the same stages and re-indexings as
`normBranch`, without centering. -/
noncomputable def normBranchInt (sh : NormShape) :
    TableKernel (sh.f 0) (sh.F 0) branchRows (sh.F 3) :=
  (stage EntryLaw.ternary branchRows).andThen
    (TableKernel.ofFun (reshape sh.e₁)) |>.andThen
    (stage EntryLaw.ternary branchRows) |>.andThen
    (TableKernel.ofFun (reshape sh.e₂)) |>.andThen
    (stage EntryLaw.ternary branchRows) |>.andThen
    (TableKernel.ofFun (reshape sh.e₃)) |>.andThen
    (stage EntryLaw.ternary branchRows)

/-- The norm check modulo `p`: `numBranches` independent copies of `normBranch p sh` on the same
input, stacked, re-indexed by `sh.e₄`, and followed by a ternary final stage with `finalRows` rows,
centered modulo `p`. Spec (3.1). -/
noncomputable def normCheck (p : ℕ) (sh : NormShape) :
    TableKernel (sh.f 0) (sh.F 0) finalRows (sh.F 4) :=
  (branches (fun _ : Fin numBranches => normBranch p sh)).andThen
    (TableKernel.ofFun (reshape sh.e₄)) |>.andThen
    (stageMod p EntryLaw.ternary finalRows)

/-- The norm check over the integers: the same construction as `normCheck`, with `normBranchInt` and
without centering. -/
noncomputable def normCheckInt (sh : NormShape) :
    TableKernel (sh.f 0) (sh.F 0) finalRows (sh.F 4) :=
  (branches (fun _ : Fin numBranches => normBranchInt sh)).andThen
    (TableKernel.ofFun (reshape sh.e₄)) |>.andThen
    (stage EntryLaw.ternary finalRows)

/-- The acceptance predicate of the norm check: the centered output `ctr P.p y` has squared norm at
most `P.acceptSqNorm` (`Θ`). Spec §3.5. -/
def NormAccept (P : Params) (y : Table finalRows F) : Prop :=
  sqNorm (MultiStage.ctr P.p y) ≤ P.acceptSqNorm

/-- `normCheck p sh` is `normCheckInt sh` computed modulo `p`. -/
theorem normCheck_modOf (p : ℕ) (sh : NormShape) :
    ModOf p (normCheck p sh) (normCheckInt sh) := by
  have hreshape {f F f' F' : ℕ} (e : Fin f × Fin F ≃ Fin f' × Fin F') :
      ModOf p (TableKernel.ofFun (reshape e)) (TableKernel.ofFun (reshape e)) :=
    ModOf.ofFun _ (fun _ => ctr_reshape.symm)
  have hbranch : ModOf p (normBranch p sh) (normBranchInt sh) :=
    (((((ModOf.stage.andThen (hreshape sh.e₁)).andThen ModOf.stage).andThen
      (hreshape sh.e₂)).andThen ModOf.stage).andThen (hreshape sh.e₃)).andThen
      ModOf.stage
  exact ((ModOf.branches (fun _ => hbranch)).andThen (hreshape sh.e₄)).andThen
    ModOf.stage

/-- Every table `Y` in the support of `stage μ c X` is `A * X` for a matrix `A` whose entries have
absolute value at most `μ.bound`. -/
private theorem stage_support_witness {f F c : ℕ} (μ : EntryLaw) (X : Table f F)
    {Y : Table c F} (hY : Y ∈ (stage μ c X).support) :
    ∃ A : Matrix (Fin c) (Fin f) ℤ, (∀ i j, (A i j).natAbs ≤ μ.bound) ∧ Y = A * X := by
  rcases (PMF.mem_support_map_iff _ _ _).1 hY with ⟨A, hA, rfl⟩
  rw [EntryLaw.matrixPMF, uniformPiMap] at hA
  rcases (PMF.mem_support_map_iff _ _ _).1 hA with ⟨s, _, rfl⟩
  exact ⟨_, fun i j => μ.natAbs_value_le (s i j), rfl⟩

/-- A stage maps the zero table to the zero table: every `Y` in the support of `stage μ c 0` is
zero. -/
private theorem stage_support_zero {f F c : ℕ} (μ : EntryLaw)
    {Y : Table c F} (hY : Y ∈ (stage μ c (0 : Table f F)).support) : Y = 0 := by
  obtain ⟨A, _, rfl⟩ := stage_support_witness μ _ hY
  exact Matrix.mul_zero A

/-- Centering modulo `p` does not change whether a table is small at `τ`. -/
private theorem isSmall_ctr {f F : ℕ} (p τ : ℕ) (X : Table f F) :
    IsSmall p τ (MultiStage.ctr p X) ↔ IsSmall p τ X := by
  change (∀ i j, (MultiStage.ctr p (MultiStage.ctr p X) i j).natAbs < τ) ↔
    ∀ i j, (MultiStage.ctr p X i j).natAbs < τ
  rw [ctr_ctr]

/-- If `2 * (τ' - 1) < τ` and `X` is large at `τ`, an integer ternary stage with `c` rows maps `X`
to a table that is small at `τ'` with probability at most `(1 / 2) ^ c`. -/
private theorem stage_integer_collapse_le {f F c : ℕ} {p τ τ' : ℕ}
    (hτ : 2 * (τ' - 1) < τ) (X : Table f F) (hX : IsLarge p τ X) :
    eventProbability (stage EntryLaw.ternary c X) (IsSmall p τ') ≤
      (1 / 2 : ℝ≥0∞) ^ c := by
  have h := stage_collapse_le EntryLaw.ternary EntryLaw.ternary_noTwoConsecutiveBound
    hτ c X hX
  rw [stageMod, eventProbability_map] at h
  exact (eventProbability_congr _ (fun Y => (isSmall_ctr p τ' Y).symm)).trans_le h

/-- Apply one integer ternary stage with `c` rows to the table of a pair drawn from `Q`. The Boolean
of the result is `true` if it was `true` before or if the stage maps a table that is large at `τ` to
one that is small at `τ'`. -/
private noncomputable def extendBranch {f F : ℕ} (Q : PMF (Table f F × Bool))
    (p τ τ' c : ℕ) : PMF (Table c F × Bool) := by
  classical
  exact Q.bind fun z => (stage EntryLaw.ternary c z.1).map fun Y =>
    (Y, z.2 || decide (IsLarge p τ z.1 ∧ IsSmall p τ' Y))

/-- The properties that the proof of `normCheck_accept_le_comparison` maintains for a law `Q` on
pairs of an integer table and a Boolean, after `L` stages with `c` rows of a branch. The Boolean is
`true` when some stage so far has collapsed its input, `τ` is the current threshold, `s` is the
squared norm of the branch input and `D` is the comparison law of one stage. -/
private structure BranchInvariant {f F : ℕ} (Q : PMF (Table f F × Bool))
    (p τ c L : ℕ) (s : ℚ≥0) (D : PMF ℚ≥0) : Prop where
  /-- The Boolean is `false` with probability at least `(1 - (1 / 2) ^ c) ^ L`. -/
  survival : (1 - (1 / 2 : ℝ≥0∞) ^ c) ^ L ≤ eventProbability Q (fun z => z.2 = false)
  /-- The ratio `sqNorm z.1 / s` is stochastically at least the product of `L` independent draws
  from `D`. -/
  domination : StochGe Q (fun z => (sqNorm z.1 : ℚ≥0) / s) (iidProd D L)
  /-- No overflow has occurred: a table in the support of `Q` whose Boolean is `false` and which is
  small at `τ` is its own centering modulo `p`. -/
  ctr_eq_self : ∀ z ∈ Q.support, z.2 = false → IsSmall p τ z.1 → MultiStage.ctr p z.1 = z.1

/-- The `ctr_eq_self` property of `BranchInvariant` carries over from `Q` at `τ` to
`extendBranch Q p τ τ' c` at `τ'` when `f * (τ - 1) ≤ (p - 1) / 2`. -/
private theorem extendBranch_ctr_eq_self {f F c : ℕ} {Q : PMF (Table f F × Bool)}
    {p τ τ' L : ℕ} {s : ℚ≥0} {D : PMF ℚ≥0}
    (hQ : BranchInvariant Q p τ c L s D) (hfan : f * (τ - 1) ≤ (p - 1) / 2) :
    ∀ z ∈ (extendBranch Q p τ τ' c).support,
      z.2 = false → IsSmall p τ' z.1 → MultiStage.ctr p z.1 = z.1 := by
  classical
  intro z hz hgood hsmall
  rcases (PMF.mem_support_bind_iff _ _ _).1 hz with ⟨x, hx, hz⟩
  rcases (PMF.mem_support_map_iff _ _ _).1 hz with ⟨Y, hY, rfl⟩
  have hxgood : x.2 = false := by simpa using (Bool.or_eq_false_iff.1 hgood).1
  have hxsmall : IsSmall p τ x.1 := by
    apply not_isLarge_iff_isSmall.mp
    intro hlarge
    simpa [hlarge, hsmall] using (Bool.or_eq_false_iff.1 hgood).2
  obtain ⟨A, hA, rfl⟩ := stage_support_witness EntryLaw.ternary _ hY
  rw [ctr_mul_eq_mul_ctr A x.1 hA hxsmall (by simpa [EntryLaw.ternary] using hfan)]
  rw [hQ.ctr_eq_self x hx hxgood hxsmall]

/-- The `survival` property of `BranchInvariant` carries over from `Q` to `extendBranch Q p τ τ' c`
when `2 * (τ' - 1) < τ`: the Boolean stays `false` with probability at least
`(1 - (1 / 2) ^ c) ^ (L + 1)`. -/
private theorem extendBranch_survival {f F c : ℕ} {Q : PMF (Table f F × Bool)}
    {p τ τ' L : ℕ} {s : ℚ≥0} {D : PMF ℚ≥0}
    (hQ : BranchInvariant Q p τ c L s D) (hτ : 2 * (τ' - 1) < τ) :
    (1 - (1 / 2 : ℝ≥0∞) ^ c) ^ (L + 1) ≤
      eventProbability (extendBranch Q p τ τ' c) (fun z => z.2 = false) := by
  classical
  let δ : ℝ≥0∞ := (1 / 2) ^ c
  have hcond (x : Table f F × Bool) :
      (if x.2 = false then 1 - δ else 0) ≤
        eventProbability ((stage EntryLaw.ternary c x.1).map fun Y =>
          (Y, x.2 || decide (IsLarge p τ x.1 ∧ IsSmall p τ' Y)))
          (fun z => z.2 = false) := by
    rw [eventProbability_map]
    by_cases hx : x.2 = false
    · simp only [hx, ↓reduceIte, Bool.false_or, decide_eq_false_iff_not]
      rw [eventProbability_not]
      apply tsub_le_tsub_left
      by_cases hlarge : IsLarge p τ x.1
      · simpa [hlarge, δ] using stage_integer_collapse_le hτ x.1 hlarge (c := c)
      · simp [eventProbability_eq_tsum, hlarge]
    · simp [hx]
  rw [extendBranch, eventProbability_bind]
  unfold expectation
  calc
    (1 - (1 / 2 : ℝ≥0∞) ^ c) ^ (L + 1) = (1 - δ) ^ L * (1 - δ) := pow_succ _ _
    _ ≤ eventProbability Q (fun z => z.2 = false) * (1 - δ) :=
      mul_le_mul' hQ.survival le_rfl
    _ = ∑' x, Q x * (if x.2 = false then 1 - δ else 0) := by
      rw [eventProbability_eq_tsum, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro x
      by_cases hx : x.2 = false <;> simp [hx]
    _ ≤ _ := ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hcond x)

/-- The `domination` property of `BranchInvariant` carries over from `Q` with `L` draws to
`extendBranch Q p τ τ' c` with `L + 1` draws when the distribution function of `D` is at least
`smallBallBound 3 (21 / 40) c`. -/
private theorem extendBranch_domination {f F c : ℕ} {Q : PMF (Table f F × Bool)}
    {p τ τ' L : ℕ} {s : ℚ≥0} {D : PMF ℚ≥0}
    (hQ : BranchInvariant Q p τ c L s D)
    (hD : ∀ u, smallBallBound 3 (21 / 40) c u ≤ cdf D u) :
    StochGe (extendBranch Q p τ τ' c) (fun z => (sqNorm z.1 : ℚ≥0) / s)
      (iidProd D (L + 1)) := by
  classical
  have hprod := StochGe.bind_mul Q (fun x => stage EntryLaw.ternary c x.1)
    (fun x => (sqNorm x.1 : ℚ≥0) / s)
    (fun x Y => (sqNorm Y : ℚ≥0) / sqNorm x.1) hQ.domination
    (fun x hx => stage_stochGe EntryLaw.ternary EntryLaw.ternary_mgfConstant
      (by norm_num) c x.1 (by
        intro hz
        apply hx
        simp [hz, sqNorm]) hD)
  rw [mulLaw_comm, ← iidProd] at hprod
  have hm := StochGe.map hprod
    (fun z => (z.2, z.1.2 || decide (IsLarge p τ z.1.1 ∧ IsSmall p τ' z.2)))
    (fun z => (sqNorm z.1 : ℚ≥0) / s) (by
      rintro ⟨x, Y⟩ hxy
      rcases (PMF.mem_support_bind_iff _ _ _).1 hxy with ⟨x', _, hxy⟩
      rcases (PMF.mem_support_map_iff _ _ _).1 hxy with ⟨Y', hY', heq⟩
      cases heq
      dsimp
      by_cases hz : sqNorm x.1 = 0
      · have hx0 := sqNorm_eq_zero_iff.mp hz
        have hy0 := stage_support_zero EntryLaw.ternary (hx0 ▸ hY')
        simp [hy0, sqNorm]
      · have hn : (sqNorm x.1 : ℚ≥0) ≠ 0 := by exact_mod_cast hz
        field_simp)
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, extendBranch] using hm

/-- If `ctr p X = X` and `sqNorm X ≠ 0`, the law `PMF.pure (X, false)` satisfies `BranchInvariant`
with `L = 0` and `s = sqNorm X`. -/
private theorem branchInvariant_initial {f F : ℕ} (p τ c : ℕ) (X : Table f F)
    (hX : MultiStage.ctr p X = X) (hpos : (sqNorm X : ℚ≥0) ≠ 0) (D : PMF ℚ≥0) :
    BranchInvariant (PMF.pure (X, false)) p τ c 0 (sqNorm X) D := by
  constructor
  · simp [eventProbability, PMF.pure_map]
  · intro u
    simp [iidProd, cdf, eventProbability, PMF.pure_map, div_self hpos]
  · intro z hz _ _
    have hz' : z = (X, false) := by simpa using hz
    simpa [hz'] using hX

/-- If `Q` satisfies `BranchInvariant` at `τ` with `L` stages, then `extendBranch Q p τ τ' c`
satisfies it at `τ'` with `L + 1` stages, given `2 * (τ' - 1) < τ`, `f * (τ - 1) ≤ (p - 1) / 2` and
the bound `hD` on the distribution function of `D`. -/
private theorem branchInvariant_extend {f F c : ℕ} {Q : PMF (Table f F × Bool)}
    {p τ τ' L : ℕ} {s : ℚ≥0} {D : PMF ℚ≥0}
    (hQ : BranchInvariant Q p τ c L s D) (hτ : 2 * (τ' - 1) < τ)
    (hfan : f * (τ - 1) ≤ (p - 1) / 2)
    (hD : ∀ u, smallBallBound 3 (21 / 40) c u ≤ cdf D u) :
    BranchInvariant (extendBranch Q p τ τ' c) p τ' c (L + 1) s D :=
  ⟨extendBranch_survival hQ hτ, extendBranch_domination hQ hD,
    extendBranch_ctr_eq_self hQ hfan⟩

/-- Re-indexing does not change whether a table is small at `τ`. -/
private theorem isSmall_reshape {f F f' F' : ℕ} (p τ : ℕ)
    (e : Fin f × Fin F ≃ Fin f' × Fin F') (X : Table f F) :
    IsSmall p τ (reshape e X) ↔ IsSmall p τ X := by
  rw [← not_isLarge_iff_isSmall, isLarge_reshape, not_isLarge_iff_isSmall]

/-- Re-index the table of a pair drawn from `Q` by `e` and keep the Boolean. -/
private noncomputable def reshapeBranch {f F f' F' : ℕ}
    (e : Fin f × Fin F ≃ Fin f' × Fin F') (Q : PMF (Table f F × Bool)) :
    PMF (Table f' F' × Bool) := Q.map fun z => (reshape e z.1, z.2)

/-- If `Q` satisfies `BranchInvariant`, so does `reshapeBranch e Q`, with the same parameters. -/
private theorem branchInvariant_reshape {f F f' F' : ℕ} {Q : PMF (Table f F × Bool)}
    {p τ c L : ℕ} {s : ℚ≥0} {D : PMF ℚ≥0}
    (hQ : BranchInvariant Q p τ c L s D)
    (e : Fin f × Fin F ≃ Fin f' × Fin F') :
    BranchInvariant (reshapeBranch e Q) p τ c L s D := by
  constructor
  · simpa only [reshapeBranch, eventProbability_map] using hQ.survival
  · exact StochGe.map hQ.domination _ _ (fun z _ => by simp [sqNorm_reshape])
  · intro z hz hg hs
    rcases (PMF.mem_support_map_iff _ _ _).1 hz with ⟨x, hx, rfl⟩
    rw [ctr_reshape, hQ.ctr_eq_self x hx hg ((isSmall_reshape p τ e x.1).mp hs)]

/-- The law of the table of `extendBranch Q p τ τ' c` is the law of the table of `Q` followed by an
integer ternary stage with `c` rows. -/
private theorem extendBranch_marginal {f F : ℕ} (Q : PMF (Table f F × Bool))
    (p τ τ' c : ℕ) :
    (extendBranch Q p τ τ' c).map Prod.fst =
      (Q.map Prod.fst).bind (stage EntryLaw.ternary c) := by
  simp only [extendBranch, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
  congr 1
  funext x
  exact PMF.map_id _

/-- The law of the table of `reshapeBranch e Q` is the law of the table of `Q` re-indexed by `e`. -/
private theorem reshapeBranch_marginal {f F f' F' : ℕ}
    (e : Fin f × Fin F ≃ Fin f' × Fin F') (Q : PMF (Table f F × Bool)) :
    (reshapeBranch e Q).map Prod.fst = (Q.map Prod.fst).map (reshape e) := by
  simp only [reshapeBranch, PMF.map_comp, Function.comp_def]

/-- If `P.Valid` and `sh.FanInLe P` hold and the centered source `ctr P.p S` has nonzero squared
norm, there is a law `Q` on pairs of an integer table and a Boolean such that the centered table of
`Q` has law `normBranch P.p sh S` and `Q` satisfies `BranchInvariant` at the threshold `P.tau 4`
with `numBranchStages` stages, `s = sqNorm (ctr P.p S)` and `D = C.stageLaw`. -/
private theorem normBranch_law (P : Params) (hP : P.Valid)
    (sh : NormShape) (hsh : sh.FanInLe P)
    (C : ComparisonData 3 (21 / 40) branchRows finalRows numBranchStages
      (collapseFailBound (1 / 2) branchRows numBranchStages))
    (S : Table (sh.f 0) (sh.F 0)) (hs : (sqNorm (MultiStage.ctr P.p S) : ℚ≥0) ≠ 0) :
    ∃ Q : PMF (Table branchRows (sh.F 3) × Bool),
      Q.map (fun z => MultiStage.ctr P.p z.1) = normBranch P.p sh S ∧
      BranchInvariant Q P.p (P.tau 4) branchRows numBranchStages
        (sqNorm (MultiStage.ctr P.p S)) C.stageLaw := by
  let X := MultiStage.ctr P.p S
  let Q₀ := PMF.pure (X, false)
  let Q₁ := reshapeBranch sh.e₁ (extendBranch Q₀ P.p (P.tau 0) (P.tau 1) branchRows)
  let Q₂ := reshapeBranch sh.e₂ (extendBranch Q₁ P.p (P.tau 1) (P.tau 2) branchRows)
  let Q₃ := reshapeBranch sh.e₃ (extendBranch Q₂ P.p (P.tau 2) (P.tau 3) branchRows)
  let Q₄ := extendBranch Q₃ P.p (P.tau 3) (P.tau 4) branchRows
  have hfan (i : Fin 5) : sh.f i * (P.tau i.val - 1) ≤ (P.p - 1) / 2 :=
    (Nat.mul_le_mul_right _ (hsh i)).trans (hP.noOverflow i)
  have h₀ : BranchInvariant Q₀ P.p (P.tau 0) branchRows 0 (sqNorm X) C.stageLaw :=
    branchInvariant_initial _ _ _ X ctr_ctr hs C.stageLaw
  have h₁ := branchInvariant_reshape
    (branchInvariant_extend h₀ (hP.collapse 0 (by decide)) (hfan 0) C.le_cdf_stageLaw) sh.e₁
  have h₂ := branchInvariant_reshape
    (branchInvariant_extend h₁ (hP.collapse 1 (by decide)) (hfan 1) C.le_cdf_stageLaw) sh.e₂
  have h₃ := branchInvariant_reshape
    (branchInvariant_extend h₂ (hP.collapse 2 (by decide)) (hfan 2) C.le_cdf_stageLaw) sh.e₃
  have h₄ := branchInvariant_extend h₃ (hP.collapse 3 (by decide)) (hfan 3) C.le_cdf_stageLaw
  refine ⟨Q₄, ?_, h₄⟩
  have hmarg : Q₄.map Prod.fst = normBranchInt sh X := by
    dsimp only [Q₄, Q₃, Q₂, Q₁, Q₀]
    simp only [extendBranch_marginal, reshapeBranch_marginal, PMF.pure_map, PMF.pure_bind]
    simp only [normBranchInt, TableKernel.andThen, TableKernel.ofFun, PMF.bind_bind,
      PMF.map, Function.comp_def]
  have hreshape {f F f' F' : ℕ} (e : Fin f × Fin F ≃ Fin f' × Fin F') :
      ModOf P.p (TableKernel.ofFun (reshape e)) (TableKernel.ofFun (reshape e)) :=
    ModOf.ofFun _ (fun _ => ctr_reshape.symm)
  have hmod : ModOf P.p (normBranch P.p sh) (normBranchInt sh) :=
    (((((ModOf.stage.andThen (hreshape sh.e₁)).andThen ModOf.stage).andThen
      (hreshape sh.e₂)).andThen ModOf.stage).andThen (hreshape sh.e₃)).andThen ModOf.stage
  have hcenter : normBranch P.p sh X = normBranch P.p sh S := by
    have hstage : stageMod P.p EntryLaw.ternary branchRows X =
        stageMod P.p EntryLaw.ternary branchRows S := stageMod_congr ctr_ctr
    simp only [normBranch, TableKernel.andThen]
    rw [hstage]
  calc
    Q₄.map (fun z => MultiStage.ctr P.p z.1) =
        (Q₄.map Prod.fst).map (MultiStage.ctr P.p) := by rw [PMF.map_comp]; rfl
    _ = (normBranchInt sh X).map (MultiStage.ctr P.p) := by rw [hmarg]
    _ = normBranch P.p sh X := by simpa only [X, ctr_ctr] using (hmod X).symm
    _ = normBranch P.p sh S := hcenter

/-- If `Q` satisfies `BranchInvariant` with `D = C.stageLaw`, the quantity that is `0` when the
Boolean is `true` and `sqNorm z.1 / s` otherwise is stochastically at least `C.branchLaw`. -/
private theorem branch_dropped_domination {f F : ℕ} {Q : PMF (Table f F × Bool)}
    {p τ : ℕ} {s : ℚ≥0}
    (C : ComparisonData 3 (21 / 40) branchRows finalRows numBranchStages
      (collapseFailBound (1 / 2) branchRows numBranchStages))
    (hQ : BranchInvariant Q p τ branchRows numBranchStages s C.stageLaw) :
    StochGe Q (fun z => if z.2 = true then 0 else (sqNorm z.1 : ℚ≥0) / s) C.branchLaw := by
  apply StochGe.of_event Q (fun z => z.2 = true) _ _ hQ.domination C.le_cdf_branchLaw
  have heq : eventProbability Q (fun z => z.2 = true) =
      1 - eventProbability Q (fun z => z.2 = false) := by
    rw [← eventProbability_not]
    exact eventProbability_congr Q (fun z => by cases z.2 <;> simp)
  rw [heq, collapseFailBound]
  exact tsub_le_tsub_left hQ.survival _

/-- Let `Q` satisfy `BranchInvariant` at `τ` and let the pairs `x i` be in the support of `Q`. If
the stack of the centered tables is small at `τ`, then `s` times the sum over `i` of the quantity of
`branch_dropped_domination` is at most the squared norm of that stack. -/
private theorem dropped_sum_le_sqNorm {f F g : ℕ} {Q : PMF (Table f F × Bool)}
    {p τ : ℕ} {s : ℚ≥0} {D : PMF ℚ≥0}
    (hQ : BranchInvariant Q p τ branchRows numBranchStages s D)
    (x : Fin g → Table f F × Bool) (hx : ∀ i, x i ∈ Q.support)
    (hsmall : IsSmall p τ (stack (fun i => MultiStage.ctr p (x i).1))) :
    s * (∑ i, if (x i).2 = true then 0 else (sqNorm (x i).1 : ℚ≥0) / s) ≤
      (sqNorm (stack (fun i => MultiStage.ctr p (x i).1)) : ℚ≥0) := by
  rw [sqNorm_stack, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hb : (x i).2 = true
  · simp [hb]
  · have hi : IsSmall p τ (x i).1 :=
      (isSmall_ctr p τ _).mp ((isSmall_stack.mp hsmall) i)
    have heq := hQ.ctr_eq_self (x i) (hx i) (by cases h : (x i).2 <;> simp_all) hi
    rw [heq, if_neg hb]
    by_cases hs : s = 0
    · simp [hs]
    · exact le_of_eq (mul_div_cancel₀ _ hs)

/-- Let `Q` satisfy `BranchInvariant` at `τ` and let the pairs `x i` be in the support of `Q`. If
the stack of the centered tables is zero, `0 < τ` and `s ≠ 0`, then the sum over `i` of the quantity
of `branch_dropped_domination` is zero. -/
private theorem dropped_sum_eq_zero {f F g : ℕ} {Q : PMF (Table f F × Bool)}
    {p τ : ℕ} {s : ℚ≥0} {D : PMF ℚ≥0}
    (hQ : BranchInvariant Q p τ branchRows numBranchStages s D) (hτ : 0 < τ)
    (x : Fin g → Table f F × Bool) (hx : ∀ i, x i ∈ Q.support)
    (hz : stack (fun i => MultiStage.ctr p (x i).1) = 0) (hs : s ≠ 0) :
    (∑ i, if (x i).2 = true then 0 else (sqNorm (x i).1 : ℚ≥0) / s) = 0 := by
  have hsmall : IsSmall p τ (stack (fun i => MultiStage.ctr p (x i).1)) := by
    rw [hz]
    intro i j
    simpa [centeredMod] using hτ
  have he := dropped_sum_le_sqNorm hQ x hx hsmall
  rw [hz] at he
  have hnorm : sqNorm (0 : Table (g * f) F) = 0 := sqNorm_eq_zero_iff.mpr rfl
  rw [hnorm, Nat.cast_zero] at he
  exact (mul_eq_zero.mp (le_antisymm he (by positivity))).resolve_left hs

/-- If `P.Valid` holds, an accepted output `Y` of the norm check is small at `P.tau 5`. -/
private theorem normAccept_isSmall (P : Params) (hP : P.Valid)
    {F : ℕ} (Y : Table finalRows F) (hY : NormAccept P Y) :
    IsSmall P.p (P.tau 5) Y := by
  intro i j
  apply lt_of_le_of_lt _ hP.sqrtAcceptSqNorm_lt
  apply Nat.le_sqrt'.2
  exact (Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ j)).trans
    ((Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ i)).trans hY)

/-- If `P.Valid` holds and `X` is large at `P.tau 4`, the final stage modulo `P.p` maps `X` to an
accepted output with probability at most `(1 / 2) ^ finalRows`. -/
private theorem finalStage_accept_le_of_large (P : Params) (hP : P.Valid)
    {f F : ℕ} (X : Table f F) (hX : IsLarge P.p (P.tau 4) X) :
    eventProbability (stageMod P.p EntryLaw.ternary finalRows X) (NormAccept P) ≤
      (1 / 2 : ℝ≥0∞) ^ finalRows := by
  exact (eventProbability_mono_of_support _ (fun Y _ hY => normAccept_isSmall P hP Y hY)).trans
    (stage_collapse_le EntryLaw.ternary EntryLaw.ternary_noTwoConsecutiveBound
      (hP.collapse 4 (by decide)) finalRows X hX)

/-- Draw `x` from any law `Q` and apply the integer final stage to `T x`. If `P.Valid` holds, the
probability that `T x` is large at `P.tau 4` and the centered output is accepted is at most
`(1 / 2) ^ finalRows`. -/
private theorem final_large_accept_le {α : Type*} {f F : ℕ} (P : Params) (hP : P.Valid)
    (Q : PMF α) (T : α → Table f F) :
    eventProbability
      (Q.bind fun x => (stage EntryLaw.ternary finalRows (T x)).map (Prod.mk x))
      (fun z => IsLarge P.p (P.tau 4) (T z.1) ∧ NormAccept P (MultiStage.ctr P.p z.2)) ≤
        (1 / 2 : ℝ≥0∞) ^ finalRows := by
  rw [eventProbability_bind]
  unfold expectation
  calc
    _ ≤ ∑' x, Q x * (1 / 2 : ℝ≥0∞) ^ finalRows := by
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul' le_rfl
      dsimp only
      rw [eventProbability_map]
      by_cases hx : IsLarge P.p (P.tau 4) (T x)
      · have h := finalStage_accept_le_of_large P hP (T x) hx
        rw [stageMod, eventProbability_map] at h
        simpa only [hx, true_and] using h
      · simp [eventProbability_eq_tsum, hx]
    _ = _ := by rw [ENNReal.tsum_mul_right, Q.tsum_coe, one_mul]

/-- If `P.soundSqNorm ≤ s`, `s * w ≤ t` and `y ≤ P.acceptSqNorm`, then `w * (y / t) < eta`. -/
private theorem acceptance_ratio_lt (P : Params) {s t y w : ℚ≥0}
    (hs : P.soundSqNorm ≤ s) (hw : s * w ≤ t) (hy : y ≤ P.acceptSqNorm) :
    w * (y / t) < eta := by
  have heta : (0 : ℚ≥0) < eta := by norm_num [eta]
  have hspos : 0 < s := lt_of_lt_of_le (by
    unfold Params.soundSqNorm
    exact div_pos (by positivity) heta) hs
  have hthreshold : (P.acceptSqNorm : ℚ≥0) < s * eta := by
    have h := (div_le_iff₀ heta).mp hs
    have hlt : (P.acceptSqNorm : ℚ≥0) < (P.acceptSqNorm + 1 : ℕ) := by
      exact_mod_cast Nat.lt_succ_self P.acceptSqNorm
    exact hlt.trans_le h
  by_cases ht : t = 0
  · simpa [ht] using heta
  · apply (mul_lt_mul_iff_right₀ hspos).mp
    calc
      s * (w * (y / t)) = (s * w) * (y / t) := (mul_assoc _ _ _).symm
      _ ≤ t * (y / t) := mul_le_mul' hw le_rfl
      _ = y := by field_simp
      _ ≤ P.acceptSqNorm := hy
      _ < s * eta := hthreshold

/-- If `P.Valid` and `sh.FanInLe P` hold and `P.soundSqNorm ≤ sqNorm (ctr P.p S)`, then for any
comparison data `C` the norm check accepts `S` with probability at most `(1 / 2) ^ finalRows`, which
bounds the probability that the final stage collapses its input, plus the comparison probability
`C.failProb numBranches eta`. Spec §3.5, with Lemma D replaced by stochastic domination. -/
theorem normCheck_accept_le_comparison (P : Params) (hP : P.Valid)
    (sh : NormShape) (hsh : sh.FanInLe P)
    (C : ComparisonData 3 (21 / 40) branchRows finalRows numBranchStages
      (collapseFailBound (1 / 2) branchRows numBranchStages))
    (S : Table (sh.f 0) (sh.F 0))
    (hS : P.soundSqNorm ≤ sqNorm (MultiStage.ctr P.p S)) :
    eventProbability (normCheck P.p sh S) (NormAccept P) ≤
      (1 / 2 : ℝ≥0∞) ^ finalRows + C.failProb numBranches eta := by
  classical
  let s : ℚ≥0 := sqNorm (MultiStage.ctr P.p S)
  have hspos : 0 < s := lt_of_lt_of_le (by
    unfold Params.soundSqNorm
    exact div_pos (by positivity) (by norm_num [eta])) hS
  have hs : s ≠ 0 := ne_of_gt hspos
  -- A branch with a collapse contributes zero; the other branches contribute their norm ratios.
  obtain ⟨Q, hQmod, hQ⟩ := normBranch_law P hP sh hsh C S hs
  let R := piPMF (fun _ : Fin numBranches => Q)
  let T := fun x : Fin numBranches → Table branchRows (sh.F 3) × Bool =>
    reshape sh.e₄ (stack (fun i => MultiStage.ctr P.p (x i).1))
  let V := fun x : Fin numBranches → Table branchRows (sh.F 3) × Bool =>
    ∑ i, if (x i).2 = true then 0 else (sqNorm (x i).1 : ℚ≥0) / s
  -- `W` is zero outside the support of `R`, so that `W x ≠ 0` implies `T x ≠ 0` for every `x`.
  let W := fun x => if x ∈ R.support then V x else 0
  let J := R.bind fun x => (stage EntryLaw.ternary finalRows (T x)).map (Prod.mk x)
  have hsum : StochGe R W (iidSum C.branchLaw numBranches) :=
    StochGe.congr_support (StochGe.piPMF_sum Q _ C.branchLaw (branch_dropped_domination C hQ))
      (fun x hx => by simp only [W, if_pos hx]; rfl)
  have hnonzero (x) (hx : W x ≠ 0) : T x ≠ 0 := by
    have hxR : x ∈ R.support := by
      by_contra hn
      exact hx (by simp only [W, if_neg hn])
    intro hz
    have hzstack : stack (fun i => MultiStage.ctr P.p (x i).1) = 0 := by
      apply sqNorm_eq_zero_iff.mp
      rw [← sqNorm_reshape (e := sh.e₄)]
      change sqNorm (T x) = 0
      rw [hz]
      exact sqNorm_eq_zero_iff.mpr rfl
    apply hx
    rw [show W x = V x by simp only [W, if_pos hxR]]
    exact dropped_sum_eq_zero hQ (by dsimp [Params.tau]; positivity) x
      (fun i => mem_support_of_mem_support_piPMF _ hxR i) hzstack hs
  -- Multiply by the norm ratio of the final stage, whose input is nonzero by `hnonzero`.
  have hdom := StochGe.bind_mul R (fun x => stage EntryLaw.ternary finalRows (T x)) W
    (fun x Y => (sqNorm Y : ℚ≥0) / sqNorm (T x)) hsum
    (fun x hx => stage_stochGe EntryLaw.ternary EntryLaw.ternary_mgfConstant
      (by norm_num) finalRows (T x) (hnonzero x hx) C.le_cdf_finalLaw)
  rw [mulLaw_comm] at hdom
  have hTcenter (x) : MultiStage.ctr P.p (T x) = T x := by
    dsimp [T]
    rw [ctr_reshape, ctr_stack]
    congr 2
    funext i
    exact ctr_ctr
  -- The centered output of `J` has the law of `normCheck`.
  have hmargT : R.map T =
      ((branches (fun _ : Fin numBranches => normBranch P.p sh)) S).map (reshape sh.e₄) := by
    have hm := piPMF_map (fun _ : Fin numBranches => Q) (fun z => MultiStage.ctr P.p z.1)
    simp only [hQmod] at hm
    have hm' := congrArg (fun A => A.map (fun x => reshape sh.e₄ (stack x))) hm
    simpa only [R, T, branches, PMF.map_comp, Function.comp_def] using hm'
  have hmarg : J.map (fun z => MultiStage.ctr P.p z.2) = normCheck P.p sh S := by
    calc
      _ = (R.map T).bind (stageMod P.p EntryLaw.ternary finalRows) := by
        simp only [J, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def, stageMod]
      _ = _ := by
        rw [hmargT]
        simp only [normCheck, TableKernel.andThen, TableKernel.ofFun, PMF.map,
          PMF.bind_bind, Function.comp_def, PMF.pure_bind]
  -- On acceptance, either the final stage collapses its input or the comparison quantity
  -- is below `eta`.
  have hcase : ∀ z ∈ J.support, NormAccept P (MultiStage.ctr P.p z.2) →
      (IsLarge P.p (P.tau 4) (T z.1) ∧ NormAccept P (MultiStage.ctr P.p z.2)) ∨
        W z.1 * ((sqNorm z.2 : ℚ≥0) / sqNorm (T z.1)) < eta := by
    rintro ⟨x, Y⟩ hz hacc
    by_cases hl : IsLarge P.p (P.tau 4) (T x)
    · exact Or.inl ⟨hl, hacc⟩
    · apply Or.inr
      have hsmall := not_isLarge_iff_isSmall.mp hl
      rcases (PMF.mem_support_bind_iff _ _ _).1 hz with ⟨x', hxR, hz⟩
      rcases (PMF.mem_support_map_iff _ _ _).1 hz with ⟨Y', hY, heq⟩
      cases heq
      have henergy : s * W x ≤ (sqNorm (T x) : ℚ≥0) := by
        rw [show W x = V x by simp only [W, if_pos hxR]]
        dsimp only [V, T]
        rw [sqNorm_reshape]
        exact dropped_sum_le_sqNorm hQ x (fun i => mem_support_of_mem_support_piPMF _ hxR i)
          ((isSmall_reshape P.p (P.tau 4) sh.e₄ _).mp hsmall)
      obtain ⟨A, hA, rfl⟩ := stage_support_witness EntryLaw.ternary _ hY
      have hctr : MultiStage.ctr P.p (A * T x) = A * T x := by
        rw [ctr_mul_eq_mul_ctr A (T x) hA hsmall (by
          simpa [EntryLaw.ternary] using
            (Nat.mul_le_mul_right (P.tau 4 - 1) (hsh 4)).trans (hP.noOverflow 4)), hTcenter]
      apply acceptance_ratio_lt P hS henergy
      have hnat : sqNorm (A * T x) ≤ P.acceptSqNorm := by
        simpa only [NormAccept, ctr_ctr, hctr] using hacc
      exact_mod_cast hnat
  rw [← hmarg, eventProbability_map]
  exact (eventProbability_mono_of_support J hcase).trans
    ((eventProbability_le_add J _ _ _ (fun _ h => h)).trans
      (add_le_add (final_large_accept_le P hP R T) (StochGe.eventProbability_lt_le hdom eta)))

/-- Soundness of the norm check: if `P.Valid` and `sh.FanInLe P` hold and
`P.soundSqNorm ≤ sqNorm (ctr P.p S)`, then `normCheck P.p sh S` is accepted with probability at most
`normCheckError`. Spec Theorem 3.1. -/
theorem normCheck_accept_le (P : Params) (hP : P.Valid)
    (sh : NormShape) (hsh : sh.FanInLe P)
    (S : Table (sh.f 0) (sh.F 0))
    (hS : P.soundSqNorm ≤ sqNorm (MultiStage.ctr P.p S)) :
    eventProbability (normCheck P.p sh S) (NormAccept P) ≤
      (normCheckError : ℝ≥0∞) := by
  obtain ⟨C, hC⟩ := normComparison_exists
  exact (normCheck_accept_le_comparison P hP sh hsh C S hS).trans hC

end CertifiedProjections.Aerie
