/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.MultiStage.Compose.FiniteLaw
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Ring

/-!
# Kernel evaluation of finite laws

Functions on lists of atoms that the kernel evaluates quickly, each proved to give the same masses
as the definition of `FiniteLaw.lean` that it replaces. An atom `(k, m)` has index `k` and mass `m`.

* `mergedPairs op xs` is a list of atoms for `op` applied to two independent draws from `xs`. It is
  built from one atom for each unordered pair of atoms of `xs`, and the masses of atoms with equal
  index are added when the lists that are merged are sorted by index. For commutative `op`, every
  predicate has the same mass under it as under `combine op ⟨xs⟩ ⟨xs⟩` (`eventMass_mergedPairs`).
* `pairMass r xs ys` is computed in one pass over the two lists. When the indices of both lists are
  nondecreasing and `r` still holds when either argument decreases, it is the sum of `p * q` over
  the pairs of an atom `(v, p)` of `xs` and an atom `(w, q)` of `ys` with `r v w`
  (`pairMass_eq_weightedSum`).
-/

open scoped ENNReal

namespace CertifiedProjections.MultiStage.FiniteLaw

/-- The weighted sum of `f` over `xs`: the sum of `m * f k` over the atoms `(k, m)` of `xs`. -/
def weightedSum (xs : List (ℕ × ℕ)) (f : ℕ → ℕ) : ℕ :=
  match xs with
  | [] => 0
  | (k, m) :: xs => m * f k + weightedSum xs f

/-- The weighted sum of `f` over `xs ++ ys` is the sum of its weighted sums over `xs` and over
`ys`. -/
private theorem weightedSum_append (xs ys : List (ℕ × ℕ)) (f : ℕ → ℕ) :
    weightedSum (xs ++ ys) f = weightedSum xs f + weightedSum ys f := by
  induction xs with
  | nil => simp [weightedSum]
  | cons a xs ih => cases a; simp [weightedSum, ih, Nat.add_assoc]

/-- The weighted sum of `f + g` over `xs` is the sum of the weighted sums of `f` and of `g` over
`xs`. -/
private theorem weightedSum_add (xs : List (ℕ × ℕ)) (f g : ℕ → ℕ) :
    weightedSum xs (fun k => f k + g k) = weightedSum xs f + weightedSum xs g := by
  induction xs with
  | nil => simp [weightedSum]
  | cons a xs ih => cases a; simp [weightedSum, ih]; ring

/-- The weighted sum of `n * f` over `xs` is `n` times the weighted sum of `f` over `xs`. -/
private theorem weightedSum_mul_left (xs : List (ℕ × ℕ)) (f : ℕ → ℕ) (n : ℕ) :
    weightedSum xs (fun k => n * f k) = n * weightedSum xs f := by
  induction xs with
  | nil => simp [weightedSum]
  | cons a xs ih => cases a; simp [weightedSum, ih]; ring

/-- If `f` and `g` agree on the index of every atom of `xs`, their weighted sums over `xs` are
equal. -/
private theorem weightedSum_congr {xs : List (ℕ × ℕ)} {f g : ℕ → ℕ}
    (h : ∀ a ∈ xs, f a.1 = g a.1) : weightedSum xs f = weightedSum xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨k,m⟩
    simp only [weightedSum]
    rw [h (k,m) (by simp), ih (by aesop)]

/-- Merges two lists of atoms into one. At each step it compares the indices of the two first atoms
and moves the atom with the smaller index to the output; if the indices are equal, it outputs one
atom with the sum of the two masses. The number `fuel` bounds the number of steps: when no steps are
left, the output ends with what is left of `xs` followed by what is left of `ys`. The function is
used on lists sorted by index, with `fuel = xs.length + ys.length`. -/
private def merge (fuel : ℕ) (xs ys : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  match fuel, xs, ys with
  | _, [], _ => ys
  | _, _, [] => xs
  | 0, _, _ => xs ++ ys
  | n + 1, (v,p)::vs, (w,q)::ws =>
      if v < w then (v,p)::merge n vs ys
      else if w < v then (w,q)::merge n xs ws
      else (v,p+q)::merge n vs ws

/-- For every `fuel`, the weighted sum of `f` over `merge fuel xs ys` is the sum of its weighted
sums over `xs` and over `ys`. -/
private theorem weightedSum_merge (fuel : ℕ) (xs ys : List (ℕ × ℕ)) (f : ℕ → ℕ) :
    weightedSum (merge fuel xs ys) f = weightedSum xs f + weightedSum ys f := by
  induction fuel generalizing xs ys with
  | zero => cases xs <;> cases ys <;> simp [merge, weightedSum, weightedSum_append, Nat.add_assoc]
  | succ n ih =>
    cases xs with
    | nil => simp [merge, weightedSum]
    | cons a xs =>
      cases ys with
      | nil => simp [merge, weightedSum]
      | cons b ys =>
        rcases a with ⟨v,p⟩; rcases b with ⟨w,q⟩
        simp only [merge]
        split <;> simp only [weightedSum, ih]
        · ring
        · split <;> simp only [weightedSum, ih]
          · ring
          · have : v = w := by omega
            subst w
            ring

/-- Merges a list of lists of atoms in adjacent pairs with `merge`: the first list with the second,
the third with the fourth, and so on. If the number of lists is odd, the last one is kept
unchanged. -/
private def mergePass : List (List (ℕ × ℕ)) → List (List (ℕ × ℕ))
  | [] => []
  | [xs] => [xs]
  | xs :: ys :: zs => merge (xs.length + ys.length) xs ys :: mergePass zs

/-- Applies `mergePass` until one list is left, and returns that list. The first argument bounds the
number of passes: if more than one list is left after that many passes, the result is the
concatenation of the lists that are left. For the empty list of lists the result is the empty
list. -/
private def mergeRounds : ℕ → List (List (ℕ × ℕ)) → List (ℕ × ℕ)
  | _, [] => []
  | _, [xs] => xs
  | 0, xs => xs.flatten
  | n + 1, xs => mergeRounds n (mergePass xs)

/-- The weighted sum of `f` over the concatenation of the lists of `mergePass xss` equals its
weighted sum over the concatenation of the lists of `xss`. -/
private theorem weightedSum_flatten_mergePass (xss : List (List (ℕ × ℕ))) (f : ℕ → ℕ) :
    weightedSum (mergePass xss).flatten f = weightedSum xss.flatten f := by
  induction xss using mergePass.induct with
  | case1 => rfl
  | case2 xs => rfl
  | case3 xs ys zs ih =>
    simp only [mergePass, List.flatten_cons, weightedSum_append, weightedSum_merge, ih]
    omega

/-- For every `n`, the weighted sum of `f` over `mergeRounds n xss` equals its weighted sum over the
concatenation of the lists of `xss`. -/
private theorem weightedSum_mergeRounds (n : ℕ) (xss : List (List (ℕ × ℕ))) (f : ℕ → ℕ) :
    weightedSum (mergeRounds n xss) f = weightedSum xss.flatten f := by
  induction n generalizing xss with
  | zero => cases xss with
    | nil => rfl
    | cons xs xss => cases xss <;> simp [mergeRounds]
  | succ n ih =>
    cases xss with
    | nil => rfl
    | cons xs xss =>
      cases xss with
      | nil => simp [mergeRounds]
      | cons ys xss => simp only [mergeRounds, ih, weightedSum_flatten_mergePass]

/-- For `xs = [(v₁, p₁), …, (vₙ, pₙ)]`, the list of `n` lists whose `i`-th member is the atom
`(op vᵢ vᵢ, pᵢ * pᵢ)` followed by the atoms `(op vᵢ vⱼ, 2 * pᵢ * pⱼ)` for `j > i`, in order. There
is one atom for each unordered pair of atoms of `xs`; the factor `2` counts the two orders of a pair
of different atoms. -/
private def pairRows (op : ℕ → ℕ → ℕ) : List (ℕ × ℕ) → List (List (ℕ × ℕ))
  | [] => []
  | (v,p) :: xs =>
      ((op v v,p*p) :: xs.map (fun (w,q) => (op v w,2*p*q))) :: pairRows op xs

/-- A list of atoms for `op` applied to two independent draws from `xs`: the lists of
`pairRows op xs`, merged into one list by `mergeRounds`. For commutative `op` it has the same
weighted sums as the list of the atoms `(op v w, p * q)` over all ordered pairs of atoms `(v, p)`,
`(w, q)` of `xs` (`weightedSum_mergedPairs`). It is used in place of that list because it has fewer
atoms: it starts from one atom for each unordered pair, and `merge` adds the masses of atoms with
equal index when its inputs are sorted by index. -/
def mergedPairs (op : ℕ → ℕ → ℕ) (xs : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  mergeRounds xs.length (pairRows op xs)

/-- The weighted sum of `f` over the list of the atoms `(op v w, p * q)`, for `(w, q)` in `xs`, is
`p` times the sum of `q * f (op v w)` over the atoms `(w, q)` of `xs`. -/
private theorem weightedSum_map_combine (xs : List (ℕ × ℕ)) (op : ℕ → ℕ → ℕ)
    (v p : ℕ) (f : ℕ → ℕ) :
    weightedSum (xs.map (fun (w,q) => (op v w,p*q))) f =
      p * weightedSum xs (fun w => f (op v w)) := by
  induction xs with
  | nil => simp [weightedSum]
  | cons a xs ih => cases a; simp [weightedSum, ih]; ring

/-- For commutative `op`, the weighted sum of `f` over the concatenation of the lists of
`pairRows op xs` is the sum of `p * q * f (op v w)` over all ordered pairs of atoms `(v, p)`,
`(w, q)` of `xs`. -/
private theorem weightedSum_pairRows (xs : List (ℕ × ℕ)) (op : ℕ → ℕ → ℕ)
    (hc : ∀ a b, op a b = op b a) (f : ℕ → ℕ) :
    weightedSum (pairRows op xs).flatten f =
      weightedSum xs (fun v => weightedSum xs (fun w => f (op v w))) := by
  induction xs with
  | nil => simp [pairRows, weightedSum]
  | cons a xs ih =>
    rcases a with ⟨v,p⟩
    simp only [pairRows, List.flatten_cons, weightedSum_append, weightedSum,
      weightedSum_map_combine, ih]
    rw [weightedSum_add, weightedSum_mul_left]
    have h : weightedSum xs (fun k => f (op k v)) = weightedSum xs (fun k => f (op v k)) := by
      apply weightedSum_congr
      intro a ha
      rw [hc]
    rw [h]
    ring

/-- For commutative `op`, the weighted sum of `f` over `mergedPairs op xs` is the sum of
`p * q * f (op v w)` over all ordered pairs of atoms `(v, p)`, `(w, q)` of `xs`. -/
theorem weightedSum_mergedPairs (op : ℕ → ℕ → ℕ) (xs : List (ℕ × ℕ))
    (hc : ∀ a b, op a b = op b a) (f : ℕ → ℕ) :
    weightedSum (mergedPairs op xs) f =
      weightedSum xs (fun v => weightedSum xs (fun w => f (op v w))) := by
  exact (weightedSum_mergeRounds _ _ _).trans (weightedSum_pairRows _ _ hc _)

/-- The weighted sum of the zero function over `xs` is zero. -/
private theorem weightedSum_zero (xs : List (ℕ × ℕ)) : weightedSum xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a; simp [weightedSum, ih]

/-- The weighted sum of `f` over `xs.reverse` equals its weighted sum over `xs`. -/
private theorem weightedSum_reverse (xs : List (ℕ × ℕ)) (f : ℕ → ℕ) :
    weightedSum xs.reverse f = weightedSum xs f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a
    simp [List.reverse_cons, weightedSum_append, weightedSum, ih, Nat.add_comm]

/-- The function that `pairMass` evaluates. Its arguments are a bound on the number of steps, a list
`xs`, a list `ys` and a number `c`. It is used with the indices of `xs` nondecreasing, the indices
of `ys` nonincreasing, and `c` the sum of the masses of `ys`. Let `(v, p)` and `(w, q)` be the first
atoms of `xs` and `ys`. If `r v w` holds, the result is `p * c` plus the result for the rest of
`xs`; otherwise it is the result for the rest of `ys` with `c - q` in place of `c`. The result is
`0` when a list is empty or no steps are left. -/
private def pairMassAux (r : ℕ → ℕ → Prop) [DecidableRel r] :
    ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ → ℕ
  | _, [], _, _ => 0
  | _, _, [], _ => 0
  | 0, _, _, _ => 0
  | n+1, (v,p)::xs, (w,q)::ys, c =>
      if r v w then p*c + pairMassAux r n xs ((w,q)::ys) c
      else pairMassAux r n ((v,p)::xs) ys (c-q)

/-- A number computed in one pass over `xs` and `ys` by `pairMassAux`. Under the hypotheses of
`pairMass_eq_weightedSum` (the indices of both lists are nondecreasing, and `r` still holds when
either argument decreases), it is the sum of `p * q` over the pairs of an atom `(v, p)` of `xs` and
an atom `(w, q)` of `ys` with `r v w`. Without these hypotheses it can differ from that sum. -/
def pairMass (r : ℕ → ℕ → Prop) [DecidableRel r]
    (xs ys : List (ℕ × ℕ)) : ℕ :=
  pairMassAux r (xs.length + ys.length) xs ys.reverse (weightedSum ys (fun _ => 1))

/-- Suppose that `r c d` implies `r a b` whenever `a ≤ c` and `b ≤ d`, that the indices of `xs` are
nondecreasing, that the indices of `ys` are nonincreasing, and that `xs.length + ys.length ≤ fuel`.
Then `pairMassAux r fuel xs ys c`, with `c` the sum of the masses of `ys`, is the sum of `p * q`
over the pairs of an atom `(v, p)` of `xs` and an atom `(w, q)` of `ys` with `r v w`. -/
private theorem pairMassAux_eq_weightedSum (r : ℕ → ℕ → Prop) [DecidableRel r]
    (hd : ∀ a b c d, a ≤ c → b ≤ d → r c d → r a b)
    (fuel : ℕ) (xs ys : List (ℕ × ℕ))
    (hf : xs.length + ys.length ≤ fuel)
    (hx : xs.Pairwise (fun a b => a.1 ≤ b.1))
    (hy : ys.Pairwise (fun a b => b.1 ≤ a.1)) :
    pairMassAux r fuel xs ys (weightedSum ys (fun _ => 1)) =
      weightedSum xs (fun v => weightedSum ys (fun w => if r v w then 1 else 0)) := by
  induction fuel generalizing xs ys with
  | zero =>
    cases xs with
    | nil => rfl
    | cons a xs => simp only [List.length_cons] at hf; omega
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases ys with
      | nil => simp [pairMassAux, weightedSum, weightedSum_zero]
      | cons b ys =>
        rcases a with ⟨v,p⟩
        rcases b with ⟨w,q⟩
        obtain ⟨hxv,hxt⟩ := List.pairwise_cons.mp hx
        obtain ⟨hyw,hyt⟩ := List.pairwise_cons.mp hy
        by_cases hr : r v w
        · have hall : weightedSum ((w,q)::ys) (fun k => if r v k then 1 else 0) =
              weightedSum ((w,q)::ys) (fun _ => 1) := by
            apply weightedSum_congr
            intro a ha
            have hra : r v a.1 := by
              rcases List.mem_cons.mp ha with h | h
              · subst a; exact hr
              · exact hd v a.1 v w le_rfl (hyw a h) hr
            simp [hra]
          simp only [pairMassAux, if_pos hr]
          change p * weightedSum ((w,q)::ys) (fun _ => 1) +
            pairMassAux r n xs ((w,q)::ys) (weightedSum ((w,q)::ys) (fun _ => 1)) =
            p * weightedSum ((w,q)::ys) (fun k => if r v k then 1 else 0) +
            weightedSum xs (fun v => weightedSum ((w,q)::ys) (fun k => if r v k then 1 else 0))
          rw [ih xs ((w,q)::ys) (by simp only [List.length_cons] at hf ⊢; omega) hxt hy]
          rw [hall]
        · have hall : weightedSum ((v,p)::xs) (fun k => if r k w then 1 else 0) = 0 := by
            calc
              weightedSum ((v,p)::xs) (fun k => if r k w then 1 else 0) =
                  weightedSum ((v,p)::xs) (fun _ => 0) := by
                apply weightedSum_congr
                intro a ha
                have hra : ¬ r a.1 w := by
                  intro h
                  apply hr
                  rcases List.mem_cons.mp ha with he | he
                  · subst a; exact h
                  · exact hd v w a.1 w (hxv a he) le_rfl h
                simp [hra]
              _ = 0 := weightedSum_zero _
          simp only [pairMassAux, if_neg hr]
          have hsub : weightedSum ((w,q)::ys) (fun _ => 1) - q =
              weightedSum ys (fun _ => 1) := by simp [weightedSum]
          rw [hsub, ih ((v,p)::xs) ys (by simp only [List.length_cons] at hf ⊢; omega) hx hyt]
          simp only [weightedSum]
          have hw : weightedSum xs (fun k => q * (if r k w then 1 else 0) +
                weightedSum ys (fun l => if r k l then 1 else 0)) =
              weightedSum xs (fun k => weightedSum ys (fun l => if r k l then 1 else 0)) := by
            rw [weightedSum_add, weightedSum_mul_left]
            have htail : weightedSum xs (fun k => if r k w then 1 else 0) = 0 := by
              simp only [weightedSum, if_neg hr, Nat.mul_zero, Nat.zero_add] at hall
              exact hall
            rw [htail]
            simp
          rw [if_neg hr, hw]
          simp

/-- Suppose that `r c d` implies `r a b` whenever `a ≤ c` and `b ≤ d`, and that the indices of `xs`
and of `ys` are nondecreasing. Then `pairMass r xs ys` is the sum of `p * q` over the pairs of an
atom `(v, p)` of `xs` and an atom `(w, q)` of `ys` with `r v w`. -/
theorem pairMass_eq_weightedSum (r : ℕ → ℕ → Prop) [DecidableRel r]
    (hd : ∀ a b c d, a ≤ c → b ≤ d → r c d → r a b)
    (xs ys : List (ℕ × ℕ))
    (hx : xs.Pairwise (fun a b => a.1 ≤ b.1))
    (hy : ys.Pairwise (fun a b => a.1 ≤ b.1)) :
    pairMass r xs ys =
      weightedSum xs (fun v => weightedSum ys (fun w => if r v w then 1 else 0)) := by
  unfold pairMass
  rw [← weightedSum_reverse ys (fun _ => 1)]
  rw [pairMassAux_eq_weightedSum r hd _ xs ys.reverse (by simp) hx]
  · apply weightedSum_congr
    intro a ha
    exact weightedSum_reverse _ _
  · exact List.pairwise_reverse.mpr hy

/-- `D.total` is the weighted sum of the constant function `1` over the atoms of `D`. -/
theorem total_eq_weightedSum (D : FiniteLaw) :
    D.total = weightedSum D.atoms (fun _ => 1) := by
  unfold total
  induction D.atoms with
  | nil => rfl
  | cons a xs ih => cases a; simp [weightedSum, ih]

/-- `D.eventMass P` is the weighted sum of the indicator of `P` over the atoms of `D`. -/
theorem eventMass_eq_weightedSum (D : FiniteLaw)
    (P : ℕ → Prop) [DecidablePred P] :
    D.eventMass P = weightedSum D.atoms (fun k => if P k then 1 else 0) := by
  unfold eventMass
  induction D.atoms with
  | nil => rfl
  | cons a xs ih => cases a; simp [weightedSum, ih, mul_ite]

/-- The weighted sum of `f` over the atoms of `combine op D E` is the sum of `p * q * f (op v w)`
over the pairs of an atom `(v, p)` of `D` and an atom `(w, q)` of `E`. -/
theorem weightedSum_combine (op : ℕ → ℕ → ℕ)
    (D E : FiniteLaw) (f : ℕ → ℕ) :
    weightedSum (combine op D E).atoms f =
      weightedSum D.atoms (fun v => weightedSum E.atoms (fun w => f (op v w))) := by
  unfold combine
  induction D.atoms with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨v,p⟩
    simp only [List.flatMap_cons, weightedSum_append, weightedSum_map_combine, ih, weightedSum]

/-- For commutative `op`, the finite law with atoms `mergedPairs op D.atoms` has total mass
`D.total ^ 2`. -/
theorem total_mergedPairs (op : ℕ → ℕ → ℕ) (D : FiniteLaw)
    (hc : ∀ a b, op a b = op b a) :
    (⟨mergedPairs op D.atoms⟩ : FiniteLaw).total = D.total ^ 2 := by
  rw [total_eq_weightedSum, weightedSum_mergedPairs op D.atoms hc]
  simp only [← total_eq_weightedSum]
  have h := weightedSum_mul_left D.atoms (fun _ => 1) D.total
  simp only [Nat.mul_one, ← total_eq_weightedSum] at h
  rw [h]
  ring

/-- For commutative `op`, the finite law with atoms `mergedPairs op D.atoms` and the finite law
`combine op D D` have the same `eventMass P` for every predicate `P`. -/
theorem eventMass_mergedPairs (op : ℕ → ℕ → ℕ)
    (D : FiniteLaw) (hc : ∀ a b, op a b = op b a)
    (P : ℕ → Prop) [DecidablePred P] :
    (⟨mergedPairs op D.atoms⟩ : FiniteLaw).eventMass P =
      (combine op D D).eventMass P := by
  rw [eventMass_eq_weightedSum, eventMass_eq_weightedSum, weightedSum_combine]
  exact weightedSum_mergedPairs op D.atoms hc _

/-- Suppose that `P (op c d)` implies `P (op a b)` whenever `a ≤ c` and `b ≤ d`, and that the
indices of the atoms of `D` and of `E` are nondecreasing. Then
`pairMass (fun v w => P (op v w)) D.atoms E.atoms = (combine op D E).eventMass P`. -/
theorem pairMass_eq_eventMass_combine (op : ℕ → ℕ → ℕ)
    (D E : FiniteLaw) (P : ℕ → Prop) [DecidablePred P]
    (hd : ∀ a b c d, a ≤ c → b ≤ d → P (op c d) → P (op a b))
    (hx : D.atoms.Pairwise (fun a b => a.1 ≤ b.1))
    (hy : E.atoms.Pairwise (fun a b => a.1 ≤ b.1)) :
    pairMass (fun v w => P (op v w)) D.atoms E.atoms = (combine op D E).eventMass P := by
  rw [pairMass_eq_weightedSum _ hd _ _ hx hy, eventMass_eq_weightedSum, weightedSum_combine]

/-- For commutative `op`, the finite law with atoms `mergedPairs op D.atoms` and the finite law
`combine op D D` give the same probability law for every `unit`. -/
private theorem toPMF_mergedPairs (op : ℕ → ℕ → ℕ)
    (D : FiniteLaw) (hc : ∀ a b, op a b = op b a)
    (unit : ℚ≥0) :
    (⟨mergedPairs op D.atoms⟩ : FiniteLaw).toPMF unit =
      (combine op D D).toPMF unit := by
  apply toPMF_eq_of_eventMass
  · rw [total_mergedPairs op D hc, total_combine]
    ring
  · intro P hP
    exact eventMass_mergedPairs op D hc P

/-- If `D.total ≠ 0`, the finite law with atoms `mergedPairs (· * ·) D.atoms`, read with unit
`unit * unit`, is the law of the product of two independent draws from `D.toPMF unit`. -/
theorem toPMF_mergedPairs_mul (D : FiniteLaw) (unit : ℚ≥0)
    (hD : D.total ≠ 0) :
    (⟨mergedPairs (· * ·) D.atoms⟩ : FiniteLaw).toPMF
        (unit * unit) = mulLaw (D.toPMF unit) (D.toPMF unit) := by
  rw [toPMF_mergedPairs (· * ·) D Nat.mul_comm]
  exact toPMF_mul D D unit unit hD hD

/-- If `D.total ≠ 0`, the finite law with atoms `mergedPairs (· + ·) D.atoms`, read with unit
`unit`, is the law of the sum of two independent draws from `D.toPMF unit`. -/
theorem toPMF_mergedPairs_add (D : FiniteLaw) (unit : ℚ≥0)
    (hD : D.total ≠ 0) :
    (⟨mergedPairs (· + ·) D.atoms⟩ : FiniteLaw).toPMF unit =
      addLaw (D.toPMF unit) (D.toPMF unit) := by
  rw [toPMF_mergedPairs (· + ·) D Nat.add_comm]
  exact toPMF_add D D unit hD hD

/-- Let `F.total ≠ 0`, `P.total ≠ 0`, `0 < u` and `0 < v`, and let the indices of the atoms of `P`
be nondecreasing. Then the probability that a draw from `F.toPMF u` times the sum of two independent
draws from `P.toPMF v` is strictly below `n * (u * v)` is a ratio of natural numbers. The
denominator is `F.total * P.total ^ 2`. The numerator is the sum, over the atoms `(z, m)` of `F`, of
`m` times `pairMass (fun x y => z * (x + y) < n) P.atoms P.atoms`, which is the sum of `p * q` over
the pairs of atoms `(x, p)`, `(y, q)` of `P` with `z * (x + y) < n`. -/
theorem eventProbability_mulLaw_addLaw_toPMF
    (F P : FiniteLaw) (u v : ℚ≥0) (n : ℕ)
    (hF : F.total ≠ 0) (hP : P.total ≠ 0) (hu : 0 < u) (hv : 0 < v)
    (hs : P.atoms.Pairwise (fun a b => a.1 ≤ b.1)) :
    eventProbability (mulLaw (F.toPMF u) (addLaw (P.toPMF v) (P.toPMF v)))
        (· < (n : ℚ≥0) * (u * v)) =
      (weightedSum F.atoms (fun z => pairMass (fun x y => z * (x + y) < n)
        P.atoms P.atoms) : ℝ≥0∞) / (F.total * P.total ^ 2) := by
  have hPP : (P.add P).total ≠ 0 := by simp [hP]
  rw [← toPMF_add P P v hP hP, ← toPMF_mul F (P.add P) u v hF hPP,
    eventProbability_toPMF _ _ _ (by simp [hF, hP])]
  have hind : ∀ k : ℕ, (k : ℚ≥0) * (u * v) < (n : ℚ≥0) * (u * v) ↔ k < n := by
    intro k
    rw [mul_lt_mul_iff_left₀ (mul_pos hu hv)]
    exact_mod_cast Iff.rfl
  simp only [total_mul, total_add, Nat.cast_mul, pow_two]
  congr 1
  rw [eventMass_eq_weightedSum]
  simp only [hind]
  congr 1
  unfold mul
  rw [weightedSum_combine]
  apply weightedSum_congr
  intro a ha
  unfold add
  rw [weightedSum_combine]
  symm
  apply pairMass_eq_weightedSum _ _ _ _ hs hs
  intro b c d e hb hc h
  exact lt_of_le_of_lt (Nat.mul_le_mul_left a.1 (Nat.add_le_add hb hc)) h

end CertifiedProjections.MultiStage.FiniteLaw
