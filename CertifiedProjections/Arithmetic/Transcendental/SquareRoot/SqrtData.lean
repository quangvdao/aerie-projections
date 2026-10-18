/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Arithmetic.Interval.Interval
import Mathlib.Data.Nat.Sqrt

/-! Outward-rounded integer square-root evaluator. -/
namespace CertifiedProjections.Interval
variable {p : ℕ}

/-- Least natural number whose square is at least `n`. -/
def ceilSqrt (n : ℕ) : ℕ :=
  if Nat.sqrt n * Nat.sqrt n = n then Nat.sqrt n else Nat.sqrt n + 1

/-- Integer radicand used for a lower square-root endpoint. -/
def Internal.sqrtRadicand (p : ℕ) (n : ℤ) : ℕ :=
  n.toNat * Dyadic.scale p

/--
Outward-rounded square root. Soundness requires the input lower endpoint to
be nonnegative.
-/
def sqrt (I : Interval p) : Interval p :=
  ⟨Nat.sqrt (Internal.sqrtRadicand p I.lo),
    ceilSqrt (Internal.sqrtRadicand p I.hi)⟩

end CertifiedProjections.Interval
