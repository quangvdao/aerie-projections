/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Lemmas.Moments
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Prime

/-!
# Aerie parameters

The structure `Params` holds the parameters of the norm check and the ring-equation check (spec §2,
§3.1, §5 and §7). This file defines the quantities derived from them: the thresholds `Params.tau`,
the squared-norm bounds `Params.soundSqNorm`, `Params.honestSqNorm` and `Params.residualSqNorm`, and
the error bounds `Params.overflowError`, `Params.falseZeroError` and `Params.ringCheckError`. It
states the arithmetic side conditions `Params.Valid` and proves them for the two instances
`falcon512` and `falcon1024` (`falcon512_valid`, `falcon1024_valid`).

The constants `branchRows`, `finalRows`, `numBranches`, `numBranchStages`, `eta` and
`normCheckError` of the norm check are the same for both instances.
-/

open scoped BigOperators ENNReal NNReal
open CertifiedProjections.MultiStage

noncomputable section

namespace CertifiedProjections.Aerie

/-- Spec (3.1): rows in each branch stage. -/
abbrev branchRows : ℕ := 43
/-- Spec (3.1): rows in the final stage. -/
abbrev finalRows : ℕ := 156
/-- Spec (3.1): number of independent branches. -/
abbrev numBranches : ℕ := 4
/-- Spec (3.1): stages in each branch. -/
abbrev numBranchStages : ℕ := 4
/-- The comparison threshold `η` of the norm check: the soundness threshold `Params.soundSqNorm` is
`(acceptSqNorm + 1) / eta`. This is the spec's `η_proj`. `normComparison_exists` proves the
comparison bound for it, and the lift condition `Params.Valid.lift` holds with it for both
parameter sets. -/
def eta : ℚ≥0 := 2 ^ 15
/-- The error bound `2^-136` of the norm check (spec Theorem 3.1). By `normComparison_exists` there
is comparison data `C` for which `(1 / 2) ^ finalRows + C.failProb numBranches eta` is at most this
value. -/
def normCheckError : ℝ≥0 := 2⁻¹ ^ 136

/-- Spec §2, §3.1 and §5: parameters of the norm check and the ring-equation check. -/
structure Params where
  /-- The modulus `p` of both checks: the output of every stage is centered modulo `p`. -/
  p : ℕ
  /-- The Falcon modulus `q`. -/
  q : ℕ
  /-- The ring degree `n`: signatures are polynomials in `ℤ[X]/(X^n + 1)`. -/
  n : ℕ
  /-- `⌊β²⌋`, the Falcon bound on the squared norm of a signature. -/
  betaSq : ℕ
  /-- An upper bound on the number of records, counting padding records. -/
  maxSignatures : ℕ
  /-- `Θ`: the norm check accepts when the squared norm of its centered output is at most this
  value. -/
  acceptSqNorm : ℕ
  /-- Upper bounds `f₀..f₄` on the fan-ins of the norm check: `fanInMax i` for `i ≤ 3` bounds the
  fan-in of branch stage `i`, and `fanInMax 4` that of the final stage. -/
  fanInMax : Fin 5 → ℕ
  /-- A bound on the absolute value of every centered coefficient of `S₂` (see
  `Source.S2Bounded`). -/
  s2Bound : ℕ
  /-- A bound on the absolute value of the public coefficients `h` and `c`. -/
  publicBound : ℕ
  /-- `L_Δ`: a bound on the absolute value of every entry of the integer residual. -/
  residualEntryBound : ℕ
  /-- `b`: the matrix entries of the ring-equation check are uniform on the integers from `-b` to
  `b`. -/
  ringEntryBound : ℕ
  /-- `c₁, c₂, c₃`: the numbers of rows of the three stages of the ring-equation check. -/
  ringRows : Fin 3 → ℕ
  /-- The moment order used in `overflowError` (`ε_ovf`). -/
  overflowOrder : ℕ
  /-- The moment order used to bound the probability that the norm check rejects an honest
  source. -/
  honestOrder : ℕ

namespace Params
/-- Spec (3.3): `Nat.sqrt P.acceptSqNorm`, the integer square root of the acceptance bound. -/
def sqrtAcceptSqNorm (P : Params) : ℕ := Nat.sqrt P.acceptSqNorm          -- m_Θ
/-- Spec (3.3): the threshold `2 ^ (5 - i) * (2 * sqrtAcceptSqNorm + 1)` applied to the table after
`i` stages of the norm check, for `i ≤ 5`. -/
def tau (P : Params) (i : ℕ) : ℕ := 2 ^ (5 - i) * (2 * P.sqrtAcceptSqNorm + 1)  -- τ_i, i ≤ 5
/-- Spec §2: the soundness threshold `Q_S = (acceptSqNorm + 1) / eta`. `normCheck_accept_le` bounds
the acceptance probability of a source whose centered squared norm is at least this value. -/
def soundSqNorm (P : Params) : ℚ≥0 := (P.acceptSqNorm + 1 : ℕ) / eta       -- Q_S
/-- Spec §7: the bound `H_S` on the squared norm of an honest source. -/
def honestSqNorm (P : Params) : ℕ := P.maxSignatures * P.betaSq            -- H_S
/-- Spec Lemma 4.2: the bound `H_Δ` on the squared norm of the residual. -/
def residualSqNorm (P : Params) : ℕ := P.maxSignatures * P.n * P.residualEntryBound ^ 2  -- H_Δ
/-- Spec (5.1): the variance `b * (b + 1) / 3` of an entry uniform on the integers from `-b` to `b`,
with `b = ringEntryBound`. -/
def ringVariance (P : Params) : ℝ≥0 := (P.ringEntryBound * (P.ringEntryBound + 1) : ℕ) / 3  -- σ²
/-- `ε_ovf` of spec (5.3) with `H = residualSqNorm` and `t = overflowOrder`: the bound on the
probability of overflow in the ring-equation check on an input of squared norm at most `H`. -/
def overflowError (P : Params) : ℝ≥0 :=
  (4 * P.residualSqNorm : ℕ) ^ P.overflowOrder *
    (∏ i, P.ringVariance ^ P.overflowOrder *
      (chiSquareMoment (P.ringRows i) P.overflowOrder : ℝ≥0)) /
    (P.p : ℝ≥0) ^ (2 * P.overflowOrder)
/-- `ε_zero` of spec (5.3): the sum over the three stages of
`(2 * ringEntryBound + 1)⁻¹ ^ ringRows i`, the bound on the probability of a false zero in the
ring-equation check. -/
def falseZeroError (P : Params) : ℝ≥0 :=
  ∑ i, ((2 * P.ringEntryBound + 1 : ℕ) : ℝ≥0)⁻¹ ^ P.ringRows i
/-- Spec Theorem 5.3: the error bound `overflowError + falseZeroError` of the ring-equation
check. -/
def ringCheckError (P : Params) : ℝ≥0 := P.overflowError + P.falseZeroError

/-- Spec (3.4), (3.5), (4.1) and (4.2): the arithmetic side conditions on `P` assumed by the
soundness and completeness theorems. For concrete parameters, every field is a numerical statement
that is proved by computation. -/
structure Valid (P : Params) : Prop where
  /-- The Falcon modulus `q` is prime. -/
  q_prime : P.q.Prime
  /-- Twice the entry bound of the ring-equation check is less than `q`, so two distinct entry
  values are distinct mod `q`. -/
  ringEntryBound_lt : 2 * P.ringEntryBound < P.q
  /-- The ring degree is at least `4`, so that `Source.normTable` has room for the four slack
  coefficients of a record. -/
  four_le_n : 4 ≤ P.n
  /-- For each of the five stages of the norm check, `2 * (tau (i + 1) - 1) < tau i`. This is the
  threshold hypothesis of `stage_collapse_le`. -/
  collapse : ∀ i, i < 5 → 2 * (P.tau (i + 1) - 1) < P.tau i                       -- spec (3.4)
  /-- For each of the five stages of the norm check, the largest fan-in times `tau i - 1` is at most
  `(p - 1) / 2`, so the stage does not overflow on a table that is small at `tau i` (see
  `ctr_mul_eq_mul_ctr`). -/
  noOverflow : ∀ i : Fin 5, P.fanInMax i * (P.tau i.val - 1) ≤ (P.p - 1) / 2          -- spec (3.5)
  /-- The integer square root of `acceptSqNorm` is less than `tau 5`, so an accepted output of the
  norm check is small at `tau 5`. -/
  sqrtAcceptSqNorm_lt : P.sqrtAcceptSqNorm < P.tau 5
  /-- The bound `betaSq` is less than `p`. -/
  betaSq_lt : P.betaSq < P.p
  /-- The lift condition `soundSqNorm + n * s2Bound ^ 2 < p`, under which the norm identity modulo
  `p` holds over the integers (`normIdentity_lift`). -/
  lift : P.soundSqNorm + (P.n * P.s2Bound ^ 2 : ℕ) < (P.p : ℚ≥0)                  -- spec (4.1)
  /-- The bounds `Nat.sqrt betaSq` on a centered `s1` coefficient and `publicBound` on a `c`
  coefficient add up to at most `residualEntryBound`. -/
  residualEntry_le : Nat.sqrt P.betaSq + P.publicBound ≤ P.residualEntryBound
  /-- What remains of `residualEntryBound` after subtracting `Nat.sqrt betaSq` and `publicBound`
  bounds every coefficient of the product of `h` and `s2`: its square is at least
  `publicBound ^ 2 * n * betaSq`. -/
  residualEntry_sq : P.publicBound ^ 2 * P.n * P.betaSq ≤
    (P.residualEntryBound - Nat.sqrt P.betaSq - P.publicBound) ^ 2                -- spec (4.2)
  /-- Twice `residualEntryBound` is less than `p`, so the integer residual is its own centering
  modulo `p`. -/
  residualEntry_lt : 2 * P.residualEntryBound < P.p
end Params

/-- Spec §2, §3.1 and §5 instance: Falcon-512 parameters. -/
def falcon512 : Params where
  p := 2 ^ 64 - 59
  q := 12289
  n := 512
  betaSq := 34034726
  maxSignatures := 2 ^ 16
  acceptSqNorm := 5092300183991442303232
  fanInMax := ![4096, 688, 688, 688, 688]
  s2Bound := 2047
  publicBound := 6144
  residualEntryBound := 811061395
  ringEntryBound := 12
  ringRows := ![31, 31, 31]
  overflowOrder := 136
  honestOrder := 46

/-- Spec §2, §3.1 and §5 instance: Falcon-1024 parameters. -/
def falcon1024 : Params where
  p := 2 ^ 64 - 59
  q := 12289
  n := 1024
  betaSq := 70265242
  maxSignatures := 2 ^ 16
  acceptSqNorm := 10513136047130310946696
  fanInMax := ![4096, 688, 688, 688, 1376]
  s2Bound := 2047
  publicBound := 6144
  residualEntryBound := 1648068606
  ringEntryBound := 12
  ringRows := ![31, 31, 31]
  overflowOrder := 60
  honestOrder := 46

/-- The Falcon-512 parameters satisfy the arithmetic side conditions. -/
theorem falcon512_valid : falcon512.Valid := by
  constructor
  · norm_num [falcon512]
  · norm_num [falcon512]
  · norm_num [falcon512]
  · intro i hi
    interval_cases i <;> norm_num [Params.tau, Params.sqrtAcceptSqNorm, falcon512]
  · intro i
    fin_cases i <;> norm_num [Params.tau, Params.sqrtAcceptSqNorm, falcon512]
  · norm_num [Params.tau, Params.sqrtAcceptSqNorm, falcon512]
  · norm_num [falcon512]
  · norm_num [Params.soundSqNorm, eta, falcon512]
  · norm_num [falcon512]
  · norm_num [falcon512]
  · norm_num [falcon512]

/-- The Falcon-1024 parameters satisfy the arithmetic side conditions. -/
theorem falcon1024_valid : falcon1024.Valid := by
  constructor
  · norm_num [falcon1024]
  · norm_num [falcon1024]
  · norm_num [falcon1024]
  · intro i hi
    interval_cases i <;> norm_num [Params.tau, Params.sqrtAcceptSqNorm, falcon1024]
  · intro i
    fin_cases i <;> norm_num [Params.tau, Params.sqrtAcceptSqNorm, falcon1024]
  · norm_num [Params.tau, Params.sqrtAcceptSqNorm, falcon1024]
  · norm_num [falcon1024]
  · norm_num [Params.soundSqNorm, eta, falcon1024]
  · norm_num [falcon1024]
  · norm_num [falcon1024]
  · norm_num [falcon1024]

end CertifiedProjections.Aerie
