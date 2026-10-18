/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Arithmetic.Interval.Interval

/-! Executable exponential enclosures; soundness is in `Exp`. -/
namespace CertifiedProjections.Exp
variable {p : ℕ}

/-- Replace an interval's lower endpoint by zero while preserving its upper. -/
def upperHull (I : Interval p) : Interval p := ⟨0, I.hi⟩

/-- The interval base `(1 + x / 2^k)⁻¹` for a negative exponential. -/
def negBase (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  (Interval.ofRat p 1 + Interval.ofRat p (x / (2 ^ k : ℕ))).reciprocal

/-- The interval base `(1 - x / 2^k)⁻¹` for a positive exponential. -/
def posBase (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  (Interval.ofRat p (1 - x / (2 ^ k : ℕ))).reciprocal

/-- Artifact-compatible upper enclosure of `exp (-x)`. -/
def negUpper (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  upperHull ((negBase p x k).squareN k)

/-- Artifact-compatible upper enclosure of `exp x`. -/
def posUpper (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  upperHull ((posBase p x k).squareN k)

/--
Upper enclosure of `exp x` for a signed rational argument.  The branch is
decided exactly in rational arithmetic.
-/
def upper (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  if 0 ≤ x then posUpper p x k else negUpper p (-x) k

/--
Evaluate an exponential at the upper endpoint of an already-computed
interval.  This is the composition used by multivariate scalar certificates:
ordinary interval arithmetic first encloses the exponent, and this function
then encloses the exponential monotonically.
-/
def ofIntervalUpper (p : ℕ) (I : Interval p) (k : ℕ) : Interval p :=
  upper p I.upperRat k

end CertifiedProjections.Exp
