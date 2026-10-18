/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Aerie.Params
import CertifiedProjections.MultiStage.Compose.FiniteLaw
import CertifiedProjections.MultiStage.Compose.FiniteLawEval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Comparison laws for the Aerie norm check

The comparison laws `normComparison` for the norm check and the bound `normComparison_failProb_le`
on their failure probability at the threshold `eta = 2 ^ 15`. The theorem `normComparison_exists`
states the two together.

* `stageLaw` and `finalLaw` are finite laws on multiples of `1 / 512`, with total masses `2 ^ 54`
  and `2 ^ 158`. At every atom `x > 0`, the fraction of the mass strictly below `x` is at least the
  small-ball bound `(21 / 40) ^ c * exp (3 * x)`, for `c = 43` and `c = 156`. This is checked with
  rational upper bounds on `exp (3 / 512)` and `exp (3 / 8)`.
* `branchLaw` is a finite law on multiples of `1 / 2`, with total mass `2 ^ 216`. Its atoms are at
  zero and at the 86 grid points `x = m * 2 ^ j / 2` with `8 ≤ m < 16` and `x ≤ 13 * 2 ^ 10 / 2`.
  At every grid point `x`, the fraction of its mass strictly below `x` is the probability that the
  product of four independent draws from `stageLaw` is strictly below `x`, plus the collapse bound
  `1 - (1 - 2 ^ (-43)) ^ 4`, capped at one. It is computed from `stageLaw`; its masses are not
  written out in this file.
* The failure probability is the probability that a draw from `finalLaw` times the sum of four
  independent draws from `branchLaw` is strictly below `eta`. The sum of four draws is evaluated
  exactly,
  as the sum of two draws from the law of the sum of two. The result is a ratio of two natural
  numbers. One inequality between natural numbers, checked by the kernel, bounds it together with
  the final-stage term `2 ^ (-156)` by `2 ^ (-136)`.
-/

open scoped ENNReal NNReal
open CertifiedProjections.MultiStage

namespace CertifiedProjections.Aerie

/-- The comparison law for one branch stage, which has `branchRows = 43` rows. It has 24 atoms
`(k, m)`, each with mass `m` on the value `k / 512`, and total mass `2 ^ 54` (`stageLaw_total`). It
is read as a probability law with unit `1 / 512`. -/
def stageLaw : FiniteLaw :=
  ⟨[(0, 17492),
    (8, 6793),
    (64, 11049),
    (128, 16077),
    (192, 23391),
    (256, 34034),
    (320, 49520),
    (384, 72052),
    (448, 104832),
    (512, 1167224),
    (768, 5230976),
    (1024, 128512384),
    (1536, 2581221376),
    (2048, 51845136384),
    (2560, 1041342922752),
    (3072, 20916339736576),
    (3584, 76638859558912),
    (3840, 343472829628416),
    (4096, 493852519563264),
    (4224, 1045480939192320),
    (4352, 2213248187236352),
    (4480, 4685500082290688),
    (4608, 4040430354169856),
    (4672, 5093762493579264)]⟩

/-- The masses of `stageLaw` add up to `2 ^ 54`. -/
private theorem stageLaw_total : stageLaw.total = 2 ^ 54 := by
  decide +kernel

/-- The comparison law for the final stage, which has `finalRows = 156` rows. It has 36 atoms
`(k, m)`, each with mass `m` on the value `k / 512`, and total mass `2 ^ 158` (`finalLaw_total`). It
is read as a probability law with unit `1 / 512`. -/
def finalLaw : FiniteLaw :=
  ⟨[(0, 36227),
    (256, 40467),
    (384, 85666),
    (512, 73872),
    (576, 107488),
    (640, 156384),
    (704, 227544),
    (768, 331072),
    (832, 481696),
    (896, 700928),
    (960, 1019712),
    (1024, 1483776),
    (1088, 2158848),
    (1152, 3141248),
    (1216, 4570112),
    (1280, 6649856),
    (1344, 9675264),
    (1408, 14077952),
    (1472, 20482048),
    (1536, 1250102272),
    (2048, 529440014336),
    (3072, 213590543958016),
    (4096, 34849202745246744576),
    (6144, 5671970018367346384568320),
    (8192, 150244484434578200256408044376686592),
    (12288, 24452992579972764605669762392190051418112),
    (14336, 9840502815397009320179086670166228975222784),
    (15360, 188282827429308684503541925849197680269459456),
    (15872, 3781664111690868477269082585266758845592502272),
    (16384, 4445514175669588906870510839413246813957783552),
    (16512, 9411088698351786486221366358856613620848001024),
    (16640, 19922928241737295449069472311827229960405254144),
    (16768, 42177678153295949180375773165538254220779585536),
    (16896, 89289396181766798730816323998899958424757338112),
    (17024, 189023903895895378075549440043751593169878253568),
    (17152, 7125088090930534093720661988111151501160742912)]⟩

/-- The masses of `finalLaw` add up to `2 ^ 158`. -/
private theorem finalLaw_total : finalLaw.total = 2 ^ 158 := by
  decide +kernel

/-- A natural number with `exp (3 / 512) ≤ expStepBound / 2 ^ 79` (`exp_step_le`). The eighth power
of `expStepBound / 2 ^ 79` is an upper bound on `exp (3 * x)` at the atom `x = 8 / 512` of
`stageLaw`. -/
private def expStepBound : ℕ := 608015081258928243240747
/-- A natural number with `exp (3 / 8) ≤ expBlockBound / 2 ^ 79` (`exp_block_le`). The `n`-th power
of `expBlockBound / 2 ^ 79` is an upper bound on `exp (3 * x)` at an atom `x = 64 * n / 512`
(`exp_blocks_le`). -/
private def expBlockBound : ℕ := 879488344224778897433542

/-- `exp (3 / 512)` is at most `expStepBound / 2 ^ 79`. -/
private theorem exp_step_le : Real.exp (3 / 512 : ℝ) ≤ (expStepBound : ℝ) / 2 ^ 79 := by
  have h := Real.exp_bound' (x := (3 / 512 : ℝ))
    (by norm_num) (by norm_num) (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, expStepBound] at h ⊢
  exact h.trans (by norm_num)

/-- `exp (3 / 8)` is at most `expBlockBound / 2 ^ 79`. -/
private theorem exp_block_le : Real.exp (3 / 8 : ℝ) ≤ (expBlockBound : ℝ) / 2 ^ 79 := by
  have h := Real.exp_bound' (x := (3 / 8 : ℝ))
    (by norm_num) (by norm_num) (n := 40) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, expBlockBound] at h ⊢
  exact h.trans (by norm_num)

/-- For every `n`, `exp (3 * (64 * n) / 512)` is at most `(expBlockBound / 2 ^ 79) ^ n`. -/
private theorem exp_blocks_le (n : ℕ) :
    Real.exp (3 * (64 * n : ℕ) / 512 : ℝ) ≤ ((expBlockBound : ℝ) / 2 ^ 79) ^ n := by
  calc
    Real.exp (3 * (64 * n : ℕ) / 512 : ℝ) = Real.exp ((n : ℝ) * (3 / 8)) := by
      congr 1
      push_cast
      ring
    _ = Real.exp (3 / 8) ^ n := Real.exp_nat_mul _ _
    _ ≤ ((expBlockBound : ℝ) / 2 ^ 79) ^ n :=
      pow_le_pow_left₀ (Real.exp_nonneg _) exp_block_le n

/-- Let `k = 8` or let `k` be a multiple of `64`. Put `e = 8` and `E = expStepBound ^ 8` if `k = 8`,
and `e = k / 64` and `E = expBlockBound ^ e` otherwise. If the inequality
`21 ^ c * E * 2 ^ d ≤ a * (40 ^ c * (2 ^ 79) ^ e)` between natural numbers holds, then
`(21 / 40) ^ c * exp (3 * k / 512) ≤ a / 2 ^ d`. In `smallBallBound_le_cdf_of_smallBallCheck`, `k`
is the index of an atom of a finite law, `a` is the mass strictly below `k` and `2 ^ d` is the total
mass. -/
private theorem smallBall_le_of_nat (c k a d : ℕ)
    (hk : k = 8 ∨ k = 64 * (k / 64))
    (h : 21 ^ c * (if k = 8 then expStepBound ^ 8 else expBlockBound ^ (k / 64)) * 2 ^ d ≤
      a * (40 ^ c * (2 ^ 79) ^ (if k = 8 then 8 else k / 64))) :
    (21 / 40 : ℝ) ^ c * Real.exp (3 * (k : ℝ) / 512) ≤ (a : ℝ) / 2 ^ d := by
  have he : Real.exp (3 * (k : ℝ) / 512) ≤
      ((if k = 8 then expStepBound else expBlockBound : ℕ) : ℝ) ^
        (if k = 8 then 8 else k / 64) / (2 ^ 79) ^ (if k = 8 then 8 else k / 64) := by
    rcases hk with rfl | hk
    · rw [← div_pow]
      calc
        Real.exp (3 * (8 : ℝ) / 512) = Real.exp (3 / 512) ^ 8 := by
          rw [← Real.exp_nat_mul]
          congr 1
          norm_num
        _ ≤ ((expStepBound : ℝ) / 2 ^ 79) ^ 8 :=
          pow_le_pow_left₀ (Real.exp_nonneg _) exp_step_le 8
    · have hk8 : k ≠ 8 := by
        intro h
        subst k
        norm_num at hk
      simp only [if_neg hk8]
      rw [← div_pow]
      simpa only [← hk] using exp_blocks_le (k / 64)
  have hcast : (21 : ℝ) ^ c *
      ((if k = 8 then expStepBound else expBlockBound : ℕ) : ℝ) ^
        (if k = 8 then 8 else k / 64) * 2 ^ d ≤
      (a : ℝ) * (40 ^ c * (2 ^ 79) ^ (if k = 8 then 8 else k / 64)) := by
    by_cases hk8 : k = 8
    · simp only [if_pos hk8] at h ⊢
      exact_mod_cast h
    · simp only [if_neg hk8] at h ⊢
      exact_mod_cast h
  calc
    (21 / 40 : ℝ) ^ c * Real.exp (3 * (k : ℝ) / 512) ≤
        (21 / 40 : ℝ) ^ c *
          (((if k = 8 then expStepBound else expBlockBound : ℕ) : ℝ) ^
            (if k = 8 then 8 else k / 64) / (2 ^ 79) ^ (if k = 8 then 8 else k / 64)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((21 : ℝ) ^ c *
          ((if k = 8 then expStepBound else expBlockBound : ℕ) : ℝ) ^
            (if k = 8 then 8 else k / 64)) /
          (40 ^ c * (2 ^ 79) ^ (if k = 8 then 8 else k / 64)) := by
      rw [div_pow, mul_div_mul_comm]
    _ ≤ (a : ℝ) / 2 ^ d :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr hcast

/-- The Boolean that is `true` when every atom `(k, m)` of `G` either has `k = 0`, or has `k = 8` or
`k` a multiple of `64` and satisfies the inequality between natural numbers of `smallBall_le_of_nat`
with `a = G.massBelow k`. By `smallBallBound_le_cdf_of_smallBallCheck`, if `G.total = 2 ^ d` and
`smallBallCheck G c d = true`, then `smallBallBound 3 (21 / 40) c` is at most the distribution
function of `G.toPMF (1 / 512)`. -/
private def smallBallCheck (G : FiniteLaw) (c d : ℕ) : Bool :=
  G.atoms.all fun p => decide (p.1 = 0 ∨
    ((p.1 = 8 ∨ p.1 = 64 * (p.1 / 64)) ∧
      21 ^ c * (if p.1 = 8 then expStepBound ^ 8 else expBlockBound ^ (p.1 / 64)) * 2 ^ d ≤
        G.massBelow p.1 * (40 ^ c * (2 ^ 79) ^ (if p.1 = 8 then 8 else p.1 / 64))))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The check evaluates powers of `expStepBound` and `expBlockBound` against 54-bit masses.
/-- `smallBallCheck stageLaw 43 54` is `true`. By `smallBall_le_of_nat`, this gives
`(21 / 40) ^ 43 * exp (3 * k / 512) ≤ stageLaw.massBelow k / 2 ^ 54` for every atom of `stageLaw`
with index `k > 0`. -/
private theorem stageLaw_smallBallCheck : smallBallCheck stageLaw 43 54 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The check evaluates powers of `expStepBound` and `expBlockBound` against 158-bit masses.
/-- `smallBallCheck finalLaw 156 158` is `true`. By `smallBall_le_of_nat`, this gives
`(21 / 40) ^ 156 * exp (3 * k / 512) ≤ finalLaw.massBelow k / 2 ^ 158` for every atom of `finalLaw`
with index `k > 0`. -/
private theorem finalLaw_smallBallCheck : smallBallCheck finalLaw 156 158 = true := by
  decide +kernel

/-- If `G.total = 2 ^ d` and `smallBallCheck G c d = true`, then
`smallBallBound 3 (21 / 40) c u ≤ cdf (G.toPMF (1 / 512)) u` for every `u`. -/
private theorem smallBallBound_le_cdf_of_smallBallCheck (G : FiniteLaw) (c d : ℕ)
    (htotal : G.total = 2 ^ d) (hc : smallBallCheck G c d = true) :
    ∀ u, smallBallBound 3 (21 / 40) c u ≤ cdf (G.toPMF (1 / 512)) u := by
  apply FiniteLaw.smallBallBound_le_cdf_toPMF
  · rw [htotal]
    positivity
  · norm_num
  · norm_num
  · intro k m hmem hk
    simp only [smallBallCheck] at hc
    have h := List.all_eq_true.mp hc (k,m) hmem
    simp only [decide_eq_true_eq] at h
    rcases h with hzero | ⟨hgrid, hbound⟩
    · exact (by omega : False).elim
    · rw [htotal]
      have hb := smallBall_le_of_nat c k (G.massBelow k) d hgrid hbound
      push_cast
      simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hb

/-- `smallBallBound 3 (21 / 40) 43 u ≤ cdf (stageLaw.toPMF (1 / 512)) u` for every `u`. This is the
field `le_cdf_stageLaw` of `normComparison`. -/
private theorem smallBallBound_le_cdf_stageLaw :
    ∀ u, smallBallBound 3 (21 / 40) 43 u ≤ cdf (stageLaw.toPMF (1 / 512)) u :=
  smallBallBound_le_cdf_of_smallBallCheck stageLaw 43 54 stageLaw_total stageLaw_smallBallCheck

/-- `smallBallBound 3 (21 / 40) 156 u ≤ cdf (finalLaw.toPMF (1 / 512)) u` for every `u`. This is the
field `le_cdf_finalLaw` of `normComparison`. -/
private theorem smallBallBound_le_cdf_finalLaw :
    ∀ u, smallBallBound 3 (21 / 40) 156 u ≤ cdf (finalLaw.toPMF (1 / 512)) u :=
  smallBallBound_le_cdf_of_smallBallCheck finalLaw 156 158 finalLaw_total finalLaw_smallBallCheck

/-- If `0 < d` and `2 ^ 136 * (n * 2 ^ 156 + d) ≤ d * 2 ^ 156` as natural numbers, then
`(1 / 2) ^ 156 + n / d ≤ normCheckError` in `ℝ≥0∞`, where `normCheckError = 2 ^ (-136)`. -/
private theorem add_le_normCheckError_of_nat (n d : ℕ) (hd : 0 < d)
    (h : 2 ^ 136 * (n * 2 ^ 156 + d) ≤ d * 2 ^ 156) :
    (1 / 2 : ℝ≥0∞) ^ 156 + (n : ℝ≥0∞) / d ≤ (normCheckError : ℝ≥0∞) := by
  have hd' : (d : ℝ≥0) ≠ 0 := by exact_mod_cast hd.ne'
  have h' : (2 : ℝ) ^ 136 * ((n : ℝ) * 2 ^ 156 + d) ≤ d * 2 ^ 156 := by
    exact_mod_cast h
  have hn : (1 / 2 : ℝ≥0) ^ 156 + (n : ℝ≥0) / d ≤ (2⁻¹ : ℝ≥0) ^ 136 := by
    apply NNReal.coe_le_coe.mp
    push_cast
    field_simp
    norm_num at h' ⊢
    nlinarith [h']
  simpa only [ENNReal.coe_add, ENNReal.coe_pow, ENNReal.coe_div hd',
    ENNReal.coe_natCast, normCheckError, ENNReal.coe_inv_two,
    ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_one,
    ENNReal.coe_ofNat] using (ENNReal.coe_le_coe.mpr hn)


-- The remaining declarations evaluate natural numbers with up to 1179 binary digits.
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-- The natural number `(2 ^ 172 - (2 ^ 43 - 1) ^ 4) * 2 ^ 44`. Divided by `2 ^ 216`, it is
`1 - (1 - 2 ^ (-43)) ^ 4`, which is `collapseFailBound (1 / 2) branchRows numBranchStages`
(`collapseMass_div`). It is the mass that `branchMassBelow` adds to the mass of the product of four
draws from `stageLaw`. -/
private def collapseMass : ℕ := (2 ^ 172 - (2 ^ 43 - 1) ^ 4) * 2 ^ 44

/-- `collapseMass / 2 ^ 216` equals `collapseFailBound (1 / 2) branchRows numBranchStages`, which is
`1 - (1 - (1 / 2) ^ 43) ^ 4`. -/
private theorem collapseMass_div :
    (collapseMass : ℝ≥0∞) / 2 ^ 216 =
      collapseFailBound (1 / 2) branchRows numBranchStages := by
  have hn : (collapseMass : ℝ≥0) / 2 ^ 216 = 1 - (1 - (1 / 2) ^ 43) ^ 4 := by
    apply NNReal.coe_injective
    norm_num [NNReal.coe_sub_def, collapseMass]
  have hc := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hn
  simpa only [collapseFailBound, branchRows, numBranchStages, ENNReal.coe_sub,
    ENNReal.coe_pow, ENNReal.coe_one, ENNReal.coe_div (by positivity : (2 : ℝ≥0) ^ 216 ≠ 0),
    ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
    ENNReal.coe_natCast] using hc


/-- The finite law with atoms `FiniteLaw.mergedPairs (· * ·) stageLaw.atoms`. Read with unit
`(1 / 512) ^ 2`, it is the law of the product of two independent draws from
`stageLaw.toPMF (1 / 512)` (`FiniteLaw.toPMF_mergedPairs_mul`). -/
private def stagePairProduct : FiniteLaw :=
  ⟨FiniteLaw.mergedPairs (· * ·) stageLaw.atoms⟩

/-- The list of the 86 natural numbers `(8 + i % 8) * 2 ^ (i / 8)` for `i < 86`, in increasing
order: `8, 9, …, 15`, then `16, 18, …, 30`, then `32, 36, …, 60`, and so on up to `13 * 2 ^ 10`.
These are the positive indices of the atoms of `branchLaw`, where the index `k` stands for the value
`k / 2`. -/
private def branchGrid : List ℕ :=
  (List.range 86).map fun i => (8 + i % 8) * 2 ^ (i / 8)

/-- The smaller of `2 ^ 216` and `N + collapseMass`, where `N` is `FiniteLaw.pairMass` of
`stagePairProduct` with itself for the relation `2 * (v * w) < k * 512 ^ 4`. By
`eventProbability_iidProd_stageLaw_lt`, `N / 2 ^ 216` is the probability that the product of four
independent draws from `stageLaw.toPMF (1 / 512)` is strictly below `k / 2`. For `k` in
`branchGrid`, `branchMassBelow k` is the mass of `branchLaw` strictly below the index `k`
(`branchLaw_checks`). -/
private def branchMassBelow (k : ℕ) : ℕ :=
  min (2 ^ 216) (FiniteLaw.pairMass (fun v w => 2 * (v * w) < k * 512 ^ 4)
    stagePairProduct.atoms stagePairProduct.atoms + collapseMass)

/-- Turns a list of pairs `(kᵢ, cᵢ)`, where `cᵢ` is the mass strictly below the index `kᵢ`, into a
list of atoms with the same indices. The mass at `kᵢ` is `cᵢ₊₁ - cᵢ`, and the mass at the last index
is `d` minus the last of the `cᵢ`, where `d` is the total mass. The subtractions are those of `ℕ`,
which give `0` when the result would be negative. -/
private def atomsOfMassBelow (d : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | [(k, c)] => [(k, d - c)]
  | (k, c) :: (l, e) :: xs => (k, e - c) :: atomsOfMassBelow d ((l, e) :: xs)

/-- The comparison law for one branch of `numBranchStages = 4` stages, computed from `stageLaw`. It
has 87 atoms: one with index `0` and mass `branchMassBelow 8`, and one for each index `k` of
`branchGrid`, with masses such that the mass strictly below `k` is `branchMassBelow k`
(`branchLaw_checks`). The total mass is `2 ^ 216` (`branchLaw_total`). It is read as a probability
law with unit `1 / 2`, so the index `k` stands for the value `k / 2`. -/
def branchLaw : FiniteLaw :=
  ⟨(0, branchMassBelow 8) ::
    atomsOfMassBelow (2 ^ 216) (branchGrid.map fun k => (k, branchMassBelow k))⟩

/-- The finite law with atoms `FiniteLaw.mergedPairs (· + ·) branchLaw.atoms`. Read with unit
`1 / 2`, it is the law of the sum of two independent draws from `branchLaw.toPMF (1 / 2)`
(`FiniteLaw.toPMF_mergedPairs_add`). -/
private def branchPairSum : FiniteLaw :=
  ⟨FiniteLaw.mergedPairs (· + ·) branchLaw.atoms⟩

/-- The natural number `N` with `normComparison.failProb numBranches eta = N / 2 ^ 1022`
(`normComparison_failProb_eq`). It is the sum, over the atoms `(z, m)` of `finalLaw`, of `m` times
`FiniteLaw.pairMass` of `branchPairSum` with itself for the relation
`z * (v + w) < 2 ^ 15 * 2 * 512`. The relation says that the value `z / 512` times the value
`(v + w) / 2` is strictly below `eta = 2 ^ 15`. -/
private def failureNumerator : ℕ :=
  FiniteLaw.weightedSum finalLaw.atoms fun z =>
    FiniteLaw.pairMass (fun v w => z * (v + w) < 2 ^ 15 * 2 * 512)
      branchPairSum.atoms branchPairSum.atoms

/-- The natural number `2 ^ 1022`. It equals `finalLaw.total * branchPairSum.total ^ 2`, that is
`2 ^ 158 * (2 ^ 432) ^ 2`, and is the denominator in `normComparison_failProb_eq`. -/
private def failureDenominator : ℕ := 2 ^ 1022

/-- The masses of `stagePairProduct` add up to `2 ^ 108`, the square of the total mass of
`stageLaw`. -/
private theorem stagePairProduct_total : stagePairProduct.total = 2 ^ 108 := by
  rw [stagePairProduct, FiniteLaw.total_mergedPairs (· * ·) stageLaw Nat.mul_comm, stageLaw_total]
  exact (pow_mul (2 : ℕ) 54 2).symm

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
-- The kernel evaluates the 86 values of the branch law from the stage law.
/-- Four facts that the kernel checks by evaluating `branchLaw`: the masses of `branchLaw` add up to
`2 ^ 216`; for every atom of `branchLaw` with index `k ≠ 0`, the mass of `branchLaw` strictly below
`k` is `branchMassBelow k`; in the list of atoms of `stagePairProduct`, each index is at most the
next one; and the same holds for the list of atoms of `branchPairSum`. -/
private theorem branchLaw_checks :
    branchLaw.total = 2 ^ 216 ∧
    branchLaw.atoms.all
      (fun a => decide (a.1 = 0 ∨ branchLaw.massBelow a.1 = branchMassBelow a.1)) = true ∧
    stagePairProduct.atoms.IsChain (fun a b => a.1 ≤ b.1) ∧
    branchPairSum.atoms.IsChain (fun a b => a.1 ≤ b.1) := by
  decide +kernel

/-- The masses of `branchLaw` add up to `2 ^ 216`. -/
private theorem branchLaw_total : branchLaw.total = 2 ^ 216 := branchLaw_checks.1

/-- The indices of the atoms of `stagePairProduct` are nondecreasing along the list. -/
private theorem stagePairProduct_sorted : stagePairProduct.atoms.Pairwise (fun a b => a.1 ≤ b.1) :=
  branchLaw_checks.2.2.1.pairwise

/-- The indices of the atoms of `branchPairSum` are nondecreasing along the list. -/
private theorem branchPairSum_sorted : branchPairSum.atoms.Pairwise (fun a b => a.1 ≤ b.1) :=
  branchLaw_checks.2.2.2.pairwise

/-- The masses of `branchPairSum` add up to `2 ^ 432`, the square of the total mass of `branchLaw`.
-/
private theorem branchPairSum_total : branchPairSum.total = 2 ^ 432 := by
  rw [branchPairSum, FiniteLaw.total_mergedPairs (· + ·) branchLaw Nat.add_comm, branchLaw_total]
  exact (pow_mul (2 : ℕ) 216 2).symm

/-- For natural numbers `k` and `v`, the inequality `v * (1 / 512) ^ 4 < k * (1 / 2)` in
`ℚ≥0` holds if and only if `2 * v < k * 512 ^ 4` in `ℕ`. -/
private theorem mul_unit_lt_iff (k v : ℕ) :
    ((v : ℕ) : ℚ≥0) * (1 / 512) ^ 4 < (k : ℚ≥0) * (1 / 2) ↔
      2 * v < k * 512 ^ 4 := by
  rw [show ((v : ℕ) : ℚ≥0) * (1 / 512) ^ 4 = (v : ℕ) / (512 : ℚ≥0) ^ 4 by ring,
    show (k : ℚ≥0) * (1 / 2) = k / 2 by ring,
    div_lt_div_iff₀ (by norm_num) (by norm_num)]
  norm_cast
  omega

/-- For every `k`, the probability that the product of four independent draws from
`stageLaw.toPMF (1 / 512)` is strictly below `k / 2` equals `N / 2 ^ 216`, where `N` is
`FiniteLaw.pairMass` of `stagePairProduct` with itself for the relation `2 * (v * w) < k * 512 ^ 4`.
-/
private theorem eventProbability_iidProd_stageLaw_lt (k : ℕ) :
    eventProbability (iidProd (stageLaw.toPMF (1 / 512)) 4) (· < (k : ℚ≥0) * (1 / 2)) =
      (FiniteLaw.pairMass (fun v w => 2 * (v * w) < k * 512 ^ 4)
        stagePairProduct.atoms stagePairProduct.atoms : ℝ≥0∞) / 2 ^ 216 := by
  have hs : stageLaw.total ≠ 0 := by rw [stageLaw_total]; positivity
  have hp : stagePairProduct.total ≠ 0 := by rw [stagePairProduct_total]; positivity
  have hpair : stagePairProduct.toPMF ((1 / 512) ^ 2) =
      mulLaw (stageLaw.toPMF (1 / 512)) (stageLaw.toPMF (1 / 512)) := by
    simpa only [stagePairProduct, pow_two] using
      FiniteLaw.toPMF_mergedPairs_mul stageLaw (1 / 512) hs
  have hprod : (stagePairProduct.mul stagePairProduct).toPMF ((1 / 512) ^ 4) =
      iidProd (stageLaw.toPMF (1 / 512)) 4 := by
    calc
      _ = (stagePairProduct.mul stagePairProduct).toPMF (((1 / 512) ^ 2) * ((1 / 512) ^ 2)) := by
        congr 1
        ring
      _ = mulLaw (stagePairProduct.toPMF ((1 / 512) ^ 2))
          (stagePairProduct.toPMF ((1 / 512) ^ 2)) := FiniteLaw.toPMF_mul _ _ _ _ hp hp
      _ = _ := by rw [hpair, iidProd_four]
  rw [← hprod, FiniteLaw.eventProbability_toPMF _ _ _ (by
    rw [FiniteLaw.total_mul]; exact mul_ne_zero hp hp)]
  have hpred (q : ℕ) : (q : ℚ≥0) * (1 / 512) ^ 4 < (k : ℚ≥0) * (1 / 2) ↔
      2 * q < k * 512 ^ 4 := mul_unit_lt_iff k q
  simp_rw [hpred]
  have hquery := FiniteLaw.pairMass_eq_eventMass_combine (· * ·) stagePairProduct stagePairProduct
    (fun q => 2 * q < k * 512 ^ 4)
    (fun a b c d hac hbd h => (Nat.mul_le_mul_left 2 (Nat.mul_le_mul hac hbd)).trans_lt h)
    stagePairProduct_sorted stagePairProduct_sorted
  have hd : (stagePairProduct.mul stagePairProduct).total = 2 ^ 216 := by
    rw [FiniteLaw.total_mul, stagePairProduct_total]
    exact (pow_add (2 : ℕ) 108 108).symm
  rw [hd, Nat.cast_pow, Nat.cast_ofNat, hquery]
  rfl

/-- For every `u`, the distribution function at `u` of the product of four independent draws from
`stageLaw.toPMF (1 / 512)`, plus `collapseFailBound (1 / 2) branchRows numBranchStages` and capped
at one, is at most `cdf (branchLaw.toPMF (1 / 2)) u`. This is the field `le_cdf_branchLaw` of
`normComparison`. -/
private theorem min_cdf_iidProd_add_le_cdf_branchLaw :
    ∀ u, min 1 (cdf (iidProd (stageLaw.toPMF (1 / 512)) 4) u +
      collapseFailBound (1 / 2) branchRows numBranchStages) ≤
        cdf (branchLaw.toPMF (1 / 2)) u := by
  apply FiniteLaw.min_cdf_add_le_cdf_toPMF
  · rw [branchLaw_total]
    positivity
  · intro k m hm hk
    have hdata := List.all_eq_true.mp branchLaw_checks.2.1 (k, m) hm
    have hmass : branchLaw.massBelow k = branchMassBelow k := by
      have h := of_decide_eq_true hdata
      exact h.resolve_left (by omega)
    rw [hmass, branchLaw_total, eventProbability_iidProd_stageLaw_lt, ← collapseMass_div]
    unfold branchMassBelow
    rw [Nat.mono_cast.map_min, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
    rw [← ENNReal.add_div]
    simp only [div_eq_mul_inv, min_mul]
    rw [ENNReal.mul_inv_cancel (by positivity) (by finiteness)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
-- The inequality is between natural numbers with more than a thousand binary digits.
/-- The inequality `2 ^ 136 * (N * 2 ^ 156 + D) ≤ D * 2 ^ 156` between natural numbers, with
`N = failureNumerator` and `D = failureDenominator`. By `add_le_normCheckError_of_nat`, it gives
`(1 / 2) ^ 156 + N / D ≤ normCheckError`. -/
private theorem failure_budget :
    2 ^ 136 * (failureNumerator * 2 ^ 156 + failureDenominator) ≤
      failureDenominator * 2 ^ 156 := by
  decide +kernel

/-- The `ComparisonData` of the Aerie norm check: `stageLaw` and `finalLaw` read as probability laws
with unit `1 / 512`, `branchLaw` read with unit `1 / 2`, and the three lower bounds on their
distribution functions (`smallBallBound_le_cdf_stageLaw`, `smallBallBound_le_cdf_finalLaw`,
`min_cdf_iidProd_add_le_cdf_branchLaw`). -/
noncomputable def normComparison :
    ComparisonData 3 (21 / 40) branchRows finalRows numBranchStages
      (collapseFailBound (1 / 2) branchRows numBranchStages) where
  stageLaw := stageLaw.toPMF (1 / 512)
  finalLaw := finalLaw.toPMF (1 / 512)
  branchLaw := branchLaw.toPMF (1 / 2)
  le_cdf_stageLaw := smallBallBound_le_cdf_stageLaw
  le_cdf_finalLaw := smallBallBound_le_cdf_finalLaw
  le_cdf_branchLaw := min_cdf_iidProd_add_le_cdf_branchLaw

/-- `normComparison.failProb numBranches eta` equals `failureNumerator / failureDenominator`. The
left side is the probability that a draw from `finalLaw.toPMF (1 / 512)` times the sum of four
independent draws from `branchLaw.toPMF (1 / 2)` is strictly below `eta`. -/
private theorem normComparison_failProb_eq :
    normComparison.failProb numBranches eta =
      (failureNumerator : ℝ≥0∞) / failureDenominator := by
  have hF : finalLaw.total ≠ 0 := by rw [finalLaw_total]; positivity
  have hB : branchLaw.total ≠ 0 := by rw [branchLaw_total]; positivity
  have hP : branchPairSum.total ≠ 0 := by rw [branchPairSum_total]; positivity
  have hpair : branchPairSum.toPMF (1 / 2) =
      addLaw (branchLaw.toPMF (1 / 2)) (branchLaw.toPMF (1 / 2)) :=
    FiniteLaw.toPMF_mergedPairs_add branchLaw (1 / 2) hB
  have hsum : iidSum (branchLaw.toPMF (1 / 2)) 4 =
      addLaw (branchPairSum.toPMF (1 / 2)) (branchPairSum.toPMF (1 / 2)) := by
    rw [hpair, iidSum_four]
  have hp := FiniteLaw.eventProbability_mulLaw_addLaw_toPMF
    finalLaw branchPairSum (1 / 512) (1 / 2) (2 ^ 15 * 2 * 512)
    hF hP (by norm_num) (by norm_num) branchPairSum_sorted
  have heta : ((2 ^ 15 * 2 * 512 : ℕ) : ℚ≥0) * ((1 / 512) * (1 / 2)) = eta := by
    norm_num [eta]
  rw [heta] at hp
  change eventProbability (mulLaw (finalLaw.toPMF (1 / 512))
    (iidSum (branchLaw.toPMF (1 / 2)) 4)) (· < eta) = _
  rw [hsum, hp]
  change (failureNumerator : ℝ≥0∞) / (finalLaw.total * branchPairSum.total ^ 2) = _
  have hd : finalLaw.total * branchPairSum.total ^ 2 = failureDenominator := by
    rw [finalLaw_total, branchPairSum_total]
    unfold failureDenominator
    rw [← pow_mul, ← pow_add]
  rw [← Nat.cast_pow, ← Nat.cast_mul, hd]

/-- `(1 / 2) ^ finalRows + normComparison.failProb numBranches eta` is at most `normCheckError`: the
failure probability of `normComparison` at the threshold `eta = 2 ^ 15`, plus the term `2 ^ (-156)`
for the final stage, is at most `2 ^ (-136)`. -/
theorem normComparison_failProb_le :
    (1 / 2 : ℝ≥0∞) ^ finalRows + normComparison.failProb numBranches eta ≤
      (normCheckError : ℝ≥0∞) := by
  rw [normComparison_failProb_eq]
  exact add_le_normCheckError_of_nat failureNumerator failureDenominator (by
    unfold failureDenominator
    positivity) failure_budget

/-- Spec (3.14): there is a `ComparisonData` `C` for the parameters of the Aerie norm check with
`(1 / 2) ^ finalRows + C.failProb numBranches eta ≤ normCheckError`. The witness is
`normComparison`. -/
theorem normComparison_exists :
    ∃ C : ComparisonData 3 (21 / 40) branchRows finalRows numBranchStages
        (collapseFailBound (1 / 2) branchRows numBranchStages),
      (1 / 2 : ℝ≥0∞) ^ finalRows + C.failProb numBranches eta ≤
        (normCheckError : ℝ≥0∞) := by
  exact ⟨normComparison, normComparison_failProb_le⟩

end CertifiedProjections.Aerie
