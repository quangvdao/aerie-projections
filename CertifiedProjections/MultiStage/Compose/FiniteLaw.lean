/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Compose.Domination
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Finite laws given by natural masses

A `FiniteLaw` is a list of atoms `(k, m)`: mass `m` at the point `k * unit`, where the unit is
chosen when the law is read as a probability law by `FiniteLaw.toPMF`. Probabilities are then ratios
of natural numbers (`FiniteLaw.eventProbability_toPMF`). `FiniteLaw.combine` forms the law of an
operation applied to two independent draws (`FiniteLaw.toPMF_mul`, `FiniteLaw.toPMF_add`). The
last two theorems reduce a lower bound on the distribution function at every threshold to a bound
at the atoms.

The definitions in this file are the simple ones that say what a certificate means. The functions
that the kernel evaluates are in `FiniteLawEval.lean`.
-/

open scoped ENNReal NNReal

namespace CertifiedProjections.MultiStage

/-- A finitely supported law on `ℚ≥0` given by natural numbers. An atom `(k, m)` puts mass `m` on
the point `k * unit`, where `unit : ℚ≥0` is chosen when the law is read as a probability law by
`FiniteLaw.toPMF`. The number `k` is the index of the atom. Several atoms may have the same index;
their masses add. -/
structure FiniteLaw where
  /-- The list of atoms `(k, m)`: `k` is the index and `m` is the mass. -/
  atoms : List (ℕ × ℕ)

namespace FiniteLaw

/-- The total mass of `D`: the sum of the masses `m` over the atoms `(k, m)` of `D`. -/
def total (D : FiniteLaw) : ℕ := (D.atoms.map Prod.snd).sum

/-- The sum of the masses `m` over the atoms `(k, m)` of `D` whose index `k` satisfies `P`. -/
def eventMass (D : FiniteLaw) (P : ℕ → Prop) [DecidablePred P] : ℕ :=
  (D.atoms.map fun a => if P a.1 then a.2 else 0).sum

/-- The sum of the masses of the atoms of `D` with index strictly below `k`. -/
def massBelow (D : FiniteLaw) (k : ℕ) : ℕ := D.eventMass (· < k)

/-- The sum of `m * f (k * unit)` over the atoms `(k, m)` of `xs`, as an element of `ℝ≥0∞`. Divided
by the total mass, it is the expectation of `f` under `toPMF` (`expectation_toPMF_eq_atomSum`). -/
private noncomputable def atomSum (xs : List (ℕ × ℕ)) (unit : ℚ≥0)
    (f : ℚ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  match xs with
  | [] => 0
  | a :: xs => (a.2 : ℝ≥0∞) * f (a.1 * unit) + atomSum xs unit f

/-- The weighted sum `atomSum xs unit f` is the list sum of `m * f (k * unit)` over
all atoms `(k, m)` of `xs`. -/
private theorem atomSum_eq_sum_map (xs : List (ℕ × ℕ)) (unit : ℚ≥0)
    (f : ℚ≥0 → ℝ≥0∞) :
    atomSum xs unit f = (xs.map fun a => (a.2 : ℝ≥0∞) * f (a.1 * unit)).sum := by
  induction xs with
  | nil => simp [atomSum]
  | cons a xs ih => simp [atomSum, ih]

/-- The sum, over all `q : ℚ≥0`, of `atomSum xs unit` applied to the indicator of the point `q` is
the sum of the masses of `xs`. It follows that the masses of `toPMF` add up to one. -/
private theorem tsum_atomSum (xs : List (ℕ × ℕ)) (unit : ℚ≥0) :
    (∑' q : ℚ≥0, atomSum xs unit (fun x => if x = q then 1 else 0)) =
      ((xs.map Prod.snd).sum : ℝ≥0∞) := by
  induction xs with
  | nil => simp [atomSum]
  | cons a xs ih =>
    simp only [atomSum, ENNReal.tsum_add, ENNReal.tsum_mul_left, ih]
    simp

/-- The probability law on `ℚ≥0` that puts mass `m / D.total` on the point `k * unit` for every atom
`(k, m)` of `D`; the masses of atoms with the same point add. If `D.total = 0`, it is
`PMF.pure 0`. -/
noncomputable def toPMF (D : FiniteLaw) (unit : ℚ≥0) : PMF ℚ≥0 :=
  if h : D.total = 0 then PMF.pure 0 else
    ⟨fun q => atomSum D.atoms unit (fun x => if x = q then 1 else 0) / D.total, by
      rw [ENNReal.summable.hasSum_iff]
      simp only [div_eq_mul_inv, ENNReal.tsum_mul_right, tsum_atomSum]
      change (D.total : ℝ≥0∞) * (D.total : ℝ≥0∞)⁻¹ = 1
      exact ENNReal.mul_inv_cancel (by exact_mod_cast h) (by simp)⟩

/-- The sum, over all `q : ℚ≥0`, of `f q` times `atomSum xs unit` applied to the indicator of the
point `q` is `atomSum xs unit f`. -/
private theorem tsum_atomSum_mul (xs : List (ℕ × ℕ)) (unit : ℚ≥0)
    (f : ℚ≥0 → ℝ≥0∞) :
    (∑' q : ℚ≥0, atomSum xs unit (fun x => if x = q then 1 else 0) * f q) =
      atomSum xs unit f := by
  induction xs with
  | nil => simp [atomSum]
  | cons a xs ih =>
    simp only [atomSum, add_mul, ENNReal.tsum_add, ih]
    congr 1
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    simp

/-- If `D.total ≠ 0`, the expectation of `f` under `D.toPMF unit` is the weighted sum
`atomSum D.atoms unit f` divided by `D.total`. -/
private theorem expectation_toPMF_eq_atomSum (D : FiniteLaw) (unit : ℚ≥0)
    (f : ℚ≥0 → ℝ≥0∞) (hD : D.total ≠ 0) :
    expectation (D.toPMF unit) f = atomSum D.atoms unit f / D.total := by
  have hp : ∀ q, (D.toPMF unit) q =
      atomSum D.atoms unit (fun x => if x = q then 1 else 0) / D.total := by
    intro q
    simp only [toPMF, hD, ↓reduceDIte]
    rfl
  simp only [expectation, hp]
  simp_rw [div_eq_mul_inv, mul_right_comm _ _ (f _)]
  rw [ENNReal.tsum_mul_right, tsum_atomSum_mul]

/-- If `D.total ≠ 0`, the expectation of `f` under `D.toPMF unit` is the sum of `m * f (k * unit)`
over the atoms `(k, m)` of `D`, divided by `D.total`. -/
theorem expectation_toPMF (D : FiniteLaw) (unit : ℚ≥0) (f : ℚ≥0 → ℝ≥0∞)
    (hD : D.total ≠ 0) :
    expectation (D.toPMF unit) f =
      (D.atoms.map fun a => (a.2 : ℝ≥0∞) * f (a.1 * unit)).sum / D.total := by
  rw [expectation_toPMF_eq_atomSum D unit f hD, atomSum_eq_sum_map]

/-- `atomSum xs unit` applied to the indicator of `P` is the sum of the masses of the atoms `(k, m)`
of `xs` whose point `k * unit` satisfies `P`. -/
private theorem atomSum_indicator (xs : List (ℕ × ℕ)) (unit : ℚ≥0) (P : ℚ≥0 → Prop)
    [DecidablePred P] : atomSum xs unit (fun q => if P q then 1 else 0) =
      ((xs.map fun a => if P (a.1 * unit) then a.2 else 0).sum : ℝ≥0∞) := by
  induction xs with
  | nil => simp [atomSum]
  | cons a xs ih => simp [atomSum, ih, mul_ite]

/-- If `D.total ≠ 0`, the probability of `P` under `D.toPMF unit` is the sum of the masses of the
atoms `(k, m)` of `D` whose point `k * unit` satisfies `P`, divided by `D.total`. -/
theorem eventProbability_toPMF (D : FiniteLaw) (unit : ℚ≥0) (P : ℚ≥0 → Prop)
    [DecidablePred P] (hD : D.total ≠ 0) :
    eventProbability (D.toPMF unit) P =
      (D.eventMass (fun k => P (k * unit)) : ℝ≥0∞) / D.total := by
  rw [eventProbability_eq_expectation, expectation_toPMF D unit _ hD]
  congr 1
  have hr := atomSum_indicator D.atoms unit P
  have he := atomSum_eq_sum_map D.atoms unit (fun q => if P q then 1 else 0)
  simpa only [eventMass, Nat.cast_list_sum, List.map_map, Function.comp_def,
    Nat.cast_ite, Nat.cast_zero] using he.symm.trans hr

/-- If `D.total ≠ 0`, the probability of the point `q` under `D.toPMF unit` is the sum of the masses
of the atoms `(k, m)` of `D` with `k * unit = q`, divided by `D.total`. -/
theorem toPMF_apply (D : FiniteLaw) (unit q : ℚ≥0) (hD : D.total ≠ 0) :
    D.toPMF unit q = (D.eventMass (fun k => (k : ℚ≥0) * unit = q) : ℝ≥0∞) / D.total := by
  simp only [toPMF, hD, ↓reduceDIte]
  change atomSum D.atoms unit (fun x => if x = q then 1 else 0) / D.total = _
  congr 1
  simpa only [eventMass, Nat.cast_list_sum, List.map_map, Function.comp_def,
    Nat.cast_ite, Nat.cast_zero] using atomSum_indicator D.atoms unit (· = q)

/-- If `D` and `E` have the same total mass and `D.eventMass P = E.eventMass P` for every decidable
predicate `P` on indices, then `D.toPMF unit = E.toPMF unit` for every `unit`. -/
theorem toPMF_eq_of_eventMass (D E : FiniteLaw) (unit : ℚ≥0)
    (ht : D.total = E.total)
    (h : ∀ (P : ℕ → Prop) (_ : DecidablePred P), D.eventMass P = E.eventMass P) :
    D.toPMF unit = E.toPMF unit := by
  classical
  by_cases hD : D.total = 0
  · simp [toPMF, hD, ← ht]
  · apply PMF.ext
    intro q
    rw [toPMF_apply D unit q hD,
      toPMF_apply E unit q (by rwa [← ht]), h _ inferInstance, ht]

/-- The finite law with an atom `(op k l, m * n)` for every atom `(k, m)` of `D` and every atom
`(l, n)` of `E`. It stands for the law of `op` applied to independent draws from `D` and `E`;
`toPMF_combine` is the precise statement. -/
def combine (op : ℕ → ℕ → ℕ) (D E : FiniteLaw) : FiniteLaw :=
  ⟨D.atoms.flatMap fun a => E.atoms.map fun b => (op a.1 b.1, a.2 * b.2)⟩

/-- `combine (· * ·) D E`: the finite law with an atom `(k * l, m * n)` for every atom `(k, m)` of
`D` and every atom `(l, n)` of `E`. By `toPMF_mul`, it is the law of the product of independent
draws from `D` and `E`. -/
def mul (D E : FiniteLaw) : FiniteLaw := combine (· * ·) D E

/-- `combine (· + ·) D E`: the finite law with an atom `(k + l, m * n)` for every atom `(k, m)` of
`D` and every atom `(l, n)` of `E`. By `toPMF_add`, it is the law of the sum of independent draws
from `D` and `E`. -/
def add (D E : FiniteLaw) : FiniteLaw := combine (· + ·) D E

/-- The total mass of `combine op D E` is `D.total * E.total`. -/
theorem total_combine (op : ℕ → ℕ → ℕ) (D E : FiniteLaw) :
    (combine op D E).total = D.total * E.total := by
  have hh (xs : List (ℕ × ℕ)) :
      (((xs.flatMap fun a => E.atoms.map fun b => (op a.1 b.1, a.2 * b.2)).map
        Prod.snd).sum) = (xs.map Prod.snd).sum * E.total := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, ih, Nat.add_mul]
      congr 1
      simp only [List.map_map]
      exact List.sum_map_mul_left E.atoms Prod.snd a.2
  exact hh D.atoms

/-- The total mass of `D.mul E` is `D.total * E.total`. -/
@[simp] theorem total_mul (D E : FiniteLaw) : (D.mul E).total = D.total * E.total :=
  total_combine _ _ _

/-- The total mass of `D.add E` is `D.total * E.total`. -/
@[simp] theorem total_add (D E : FiniteLaw) : (D.add E).total = D.total * E.total :=
  total_combine _ _ _

/-- `atomSum` of a concatenation `xs ++ ys` is the sum of `atomSum` of `xs` and `atomSum` of `ys`.
-/
private theorem atomSum_append (xs ys : List (ℕ × ℕ)) (unit : ℚ≥0)
    (f : ℚ≥0 → ℝ≥0∞) : atomSum (xs ++ ys) unit f = atomSum xs unit f + atomSum ys unit f := by
  induction xs with
  | nil => simp [atomSum]
  | cons a xs ih => simp [atomSum, ih, add_assoc]

/-- Multiplying `f` by a constant `v` multiplies `atomSum xs unit f` by `v`. -/
private theorem atomSum_mul_left (xs : List (ℕ × ℕ)) (unit : ℚ≥0) (v : ℝ≥0∞)
    (f : ℚ≥0 → ℝ≥0∞) : atomSum xs unit (fun x => v * f x) = v * atomSum xs unit f := by
  induction xs with
  | nil => simp [atomSum]
  | cons a xs ih =>
    simp only [atomSum, ih, mul_add]
    ring

/-- If `op k l * w = opQ (k * u) (l * v)` for all `k` and `l`, then `atomSum` of the atoms of
`combine op D E` with unit `w`, applied to `f`, is `atomSum` of the atoms of `D` with unit `u`
applied to the function that sends `x` to `atomSum E.atoms v (fun y => f (opQ x y))`. -/
private theorem atomSum_combine (op : ℕ → ℕ → ℕ) (opQ : ℚ≥0 → ℚ≥0 → ℚ≥0)
    (D E : FiniteLaw) (u v w : ℚ≥0) (f : ℚ≥0 → ℝ≥0∞)
    (h : ∀ k l, (op k l : ℚ≥0) * w = opQ (k * u) (l * v)) :
    atomSum (combine op D E).atoms w f =
      atomSum D.atoms u (fun x => atomSum E.atoms v (fun y => f (opQ x y))) := by
  have hr (a : ℕ × ℕ) :
      atomSum (E.atoms.map fun b => (op a.1 b.1, a.2 * b.2)) w f =
        (a.2 : ℝ≥0∞) * atomSum E.atoms v (fun y => f (opQ (a.1 * u) y)) := by
    induction E.atoms with
    | nil => simp [atomSum]
    | cons b xs ih => simp [atomSum, ih, h, Nat.cast_mul, mul_add, mul_assoc]
  have hh (xs : List (ℕ × ℕ)) :
      atomSum (xs.flatMap fun a => E.atoms.map fun b => (op a.1 b.1, a.2 * b.2)) w f =
        atomSum xs u (fun x => atomSum E.atoms v (fun y => f (opQ x y))) := by
    induction xs with
    | nil => simp [atomSum]
    | cons a xs ih => simp [atomSum, atomSum_append, hr, ih]
  exact hh D.atoms

/-- For laws `D` and `E` on `ℚ≥0`, the probability of the point `q` under the law of `op x y`, with
`x` drawn from `D` and `y` drawn independently from `E`, is the expectation over `x` of the
expectation over `y` of the indicator of `op x y = q`. -/
private theorem bind_map_apply_eq_expectation (D E : PMF ℚ≥0)
    (op : ℚ≥0 → ℚ≥0 → ℚ≥0) (q : ℚ≥0) :
    (D.bind fun x => E.map (op x)) q = expectation D (fun x =>
      expectation E (fun y => if op x y = q then 1 else 0)) := by
  classical
  simp only [PMF.bind_apply, expectation, PMF.map_apply]
  apply tsum_congr
  intro x
  congr 1
  apply tsum_congr
  intro y
  simp only [eq_comm (a := q) (b := op x y)]
  split_ifs <;> simp

/-- Let `D.total ≠ 0` and `E.total ≠ 0`. If `op k l * w = opQ (k * u) (l * v)` for all indices `k`
and `l`, then `combine op D E` read with unit `w` is the law of `opQ x y` for independent draws `x`
from `D.toPMF u` and `y` from `E.toPMF v`. -/
theorem toPMF_combine (op : ℕ → ℕ → ℕ) (opQ : ℚ≥0 → ℚ≥0 → ℚ≥0)
    (D E : FiniteLaw) (u v w : ℚ≥0)
    (hD : D.total ≠ 0) (hE : E.total ≠ 0)
    (h : ∀ k l, (op k l : ℚ≥0) * w = opQ (k * u) (l * v)) :
    (combine op D E).toPMF w =
      (D.toPMF u).bind (fun x => (E.toPMF v).map (opQ x)) := by
  classical
  apply PMF.ext
  intro q
  have hn : (combine op D E).total ≠ 0 := by
    rw [total_combine]
    exact mul_ne_zero hD hE
  have ha : (combine op D E).toPMF w q =
      atomSum (combine op D E).atoms w (fun x => if x = q then 1 else 0) /
        (combine op D E).total := by
    simp only [toPMF, hn, ↓reduceDIte]
    rfl
  rw [ha, total_combine, bind_map_apply_eq_expectation]
  simp_rw [expectation_toPMF_eq_atomSum E v _ hE]
  rw [expectation_toPMF_eq_atomSum D u _ hD]
  simp_rw [div_eq_mul_inv, mul_comm _ ((E.total : ℝ≥0∞)⁻¹)]
  rw [atomSum_mul_left, atomSum_combine op opQ D E u v w (fun x => if x = q then 1 else 0) h]
  simp only [Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  ring

/-- If `D.total ≠ 0` and `E.total ≠ 0`, then `D.mul E` read with unit `u * v` is the law of the
product of independent draws from `D.toPMF u` and `E.toPMF v`. -/
theorem toPMF_mul (D E : FiniteLaw) (u v : ℚ≥0)
    (hD : D.total ≠ 0) (hE : E.total ≠ 0) :
    (D.mul E).toPMF (u * v) = mulLaw (D.toPMF u) (E.toPMF v) := by
  apply toPMF_combine (· * ·) (· * ·) D E u v (u * v) hD hE
  intro k l
  push_cast
  ring

/-- If `D.total ≠ 0` and `E.total ≠ 0`, then `D.add E` read with unit `unit` is the law of the sum
of independent draws from `D.toPMF unit` and `E.toPMF unit`. -/
theorem toPMF_add (D E : FiniteLaw) (unit : ℚ≥0)
    (hD : D.total ≠ 0) (hE : E.total ≠ 0) :
    (D.add E).toPMF unit = addLaw (D.toPMF unit) (E.toPMF unit) := by
  apply toPMF_combine (· + ·) (· + ·) D E unit unit unit hD hE
  intro k l
  push_cast
  ring

/-- If `P k` implies `Q k` for the index `k` of every atom of `D`, then
`D.eventMass P ≤ D.eventMass Q`. -/
private theorem eventMass_mono (D : FiniteLaw) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ a ∈ D.atoms, P a.1 → Q a.1) : D.eventMass P ≤ D.eventMass Q := by
  have hh (xs : List (ℕ × ℕ)) (h : ∀ a ∈ xs, P a.1 → Q a.1) :
      (xs.map fun a => if P a.1 then a.2 else 0).sum ≤
        (xs.map fun a => if Q a.1 then a.2 else 0).sum := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · split_ifs with hp hq
        · rfl
        · exact False.elim (hq (h a (by simp) hp))
        · exact Nat.zero_le _
        · rfl
      · exact ih (fun b hb => h b (by simp [hb]))
  exact hh D.atoms h

/-- Let `D.total ≠ 0`. If every atom of `D` with index `j < k` has its point `j * unit` at most `u`,
then `D.massBelow k / D.total ≤ cdf (D.toPMF unit) u`. -/
private theorem massBelow_le_cdf (D : FiniteLaw) (unit u : ℚ≥0) (k : ℕ)
    (hD : D.total ≠ 0)
    (h : ∀ a ∈ D.atoms, a.1 < k → (a.1 : ℚ≥0) * unit ≤ u) :
    (D.massBelow k : ℝ≥0∞) / D.total ≤ cdf (D.toPMF unit) u := by
  rw [cdf, eventProbability_toPMF D unit _ hD]
  apply ENNReal.div_le_div_right
  exact_mod_cast eventMass_mono D (· < k) (fun j => (j : ℚ≥0) * unit ≤ u) h

/-- Let `D.total ≠ 0`. If the point `k * unit` of every atom of `D` is at most `u`, then
`cdf (D.toPMF unit) u = 1`. -/
private theorem cdf_toPMF_eq_one (D : FiniteLaw) (unit u : ℚ≥0) (hD : D.total ≠ 0)
    (h : ∀ a ∈ D.atoms, (a.1 : ℚ≥0) * unit ≤ u) : cdf (D.toPMF unit) u = 1 := by
  rw [cdf, eventProbability_toPMF D unit _ hD]
  have he : D.eventMass (fun j => (j : ℚ≥0) * unit ≤ u) = D.total := by
    unfold eventMass total
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [h a ha, if_true]
  rw [he, ENNReal.div_self (by exact_mod_cast hD) (by simp)]

/-- Let `D.total ≠ 0` and let `f : ℚ≥0 → ℝ≥0∞` satisfy `f u ≤ 1` for every `u`. If
`f u ≤ D.massBelow k / D.total` for every atom `(k, m)` of `D` with `0 < k` and every
`u < k * unit`, then `f u ≤ cdf (D.toPMF unit) u` for every `u`. The theorems
`smallBallBound_le_cdf_toPMF` and `min_cdf_add_le_cdf_toPMF` are the cases of this statement that
are used. -/
private theorem le_cdf_toPMF_of_le_massBelow (D : FiniteLaw) (unit : ℚ≥0) (f : ℚ≥0 → ℝ≥0∞)
    (hD : D.total ≠ 0) (hf : ∀ u, f u ≤ 1)
    (hb : ∀ k m, (k, m) ∈ D.atoms → 0 < k →
      ∀ u, u < (k : ℚ≥0) * unit → f u ≤ (D.massBelow k : ℝ≥0∞) / D.total) :
    ∀ u, f u ≤ cdf (D.toPMF unit) u := by
  intro u
  classical
  by_cases he : ∃ k, ∃ m, (k, m) ∈ D.atoms ∧ u < (k : ℚ≥0) * unit
  · let k := Nat.find he
    obtain ⟨m, hm, hu⟩ := Nat.find_spec he
    change u < (k : ℚ≥0) * unit at hu
    have hk : 0 < k := by
      by_contra hh
      have hz : k = 0 := by omega
      simp [hz] at hu
    apply (hb k m hm hk u hu).trans
    apply massBelow_le_cdf D unit u k hD
    intro a ha hlt
    exact le_of_not_gt fun hg => Nat.find_min he hlt ⟨a.2, ha, hg⟩
  · rw [cdf_toPMF_eq_one D unit u hD]
    · exact hf u
    · intro a ha
      exact le_of_not_gt fun hg => he ⟨a.1, a.2, ha, hg⟩

/-- Let `D.total ≠ 0`, `0 ≤ t` and `0 ≤ K`. If
`K ^ c * exp (t * (k * unit)) ≤ D.massBelow k / D.total` for every atom `(k, m)` of `D` with
`0 < k`, then `smallBallBound t K c u ≤ cdf (D.toPMF unit) u` for every `u`. -/
theorem smallBallBound_le_cdf_toPMF (D : FiniteLaw) (unit : ℚ≥0)
    (t K : ℝ) (c : ℕ) (hD : D.total ≠ 0) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hb : ∀ k m, (k, m) ∈ D.atoms → 0 < k →
      K ^ c * Real.exp (t * ((k : ℚ≥0) * unit : ℚ≥0)) ≤
        (D.massBelow k : ℝ) / D.total) :
    ∀ u, smallBallBound t K c u ≤ cdf (D.toPMF unit) u := by
  apply le_cdf_toPMF_of_le_massBelow D unit _ hD (fun _ => min_le_left _ _)
  intro k m hm hk u hu
  apply (min_le_right _ _).trans
  have huReal : (u : ℝ) ≤ ((k : ℚ≥0) * unit : ℚ≥0) := by exact_mod_cast hu.le
  have hreal := (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huReal ht))
    (pow_nonneg hK c)).trans (hb k m hm hk)
  have htot : 0 < (D.total : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD
  simpa only [ENNReal.ofReal_div_of_pos htot, ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal hreal

/-- Let `D.total ≠ 0`. If, for every atom `(k, m)` of `D` with `0 < k`, the probability that a draw
from `P` is strictly below `k * unit`, plus `ε` and capped at one, is at most
`D.massBelow k / D.total`, then `min 1 (cdf P u + ε) ≤ cdf (D.toPMF unit) u` for every `u`. -/
theorem min_cdf_add_le_cdf_toPMF (D : FiniteLaw) (unit : ℚ≥0)
    (P : PMF ℚ≥0) (ε : ℝ≥0∞) (hD : D.total ≠ 0)
    (hb : ∀ k m, (k, m) ∈ D.atoms → 0 < k →
      min 1 (eventProbability P (· < (k : ℚ≥0) * unit) + ε) ≤
        (D.massBelow k : ℝ≥0∞) / D.total) :
    ∀ u, min 1 (cdf P u + ε) ≤ cdf (D.toPMF unit) u := by
  apply le_cdf_toPMF_of_le_massBelow D unit _ hD (fun _ => min_le_left _ _)
  intro k m hm hk u hu
  apply le_trans _ (hb k m hm hk)
  apply min_le_min_left
  exact add_le_add (eventProbability_mono_of_imp P fun a ha =>
    lt_of_le_of_lt ha hu) le_rfl

end FiniteLaw
end CertifiedProjections.MultiStage
