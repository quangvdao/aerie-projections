/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Arithmetic.Interval.Interval

/-! Executable interval comparisons; reflected soundness is separate. -/
namespace CertifiedProjections.Interval
variable {p : ℕ}

/-- Executable endpoint-order check. -/
def validCheck (I : Interval p) : Bool := decide (I.lo ≤ I.hi)

/-- Executable strict comparison between an upper endpoint and a rational. -/
def upperLTCheck (I : Interval p) (bound : ℚ) : Bool :=
  decide (I.upperRat < bound)

/-- Executable strict comparison between a rational and a lower endpoint. -/
def lowerGTCheck (I : Interval p) (bound : ℚ) : Bool :=
  decide (bound < I.lowerRat)

/-- Executable nonnegative-lower-endpoint check. -/
def nonnegCheck (I : Interval p) : Bool := decide (0 ≤ I.lo)

end CertifiedProjections.Interval
