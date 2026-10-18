/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Arithmetic.Interval.ReflectionData
import CertifiedProjections.Arithmetic.Transcendental.Exponential.Exp
import CertifiedProjections.Arithmetic.Transcendental.SquareRoot.Sqrt

/-!
# Proof-producing numeric reflection

The Boolean checks in this module are executable, but their results become
theorems only through small soundness lemmas.  Concrete certificates close
the Boolean equality with kernel reduction (`rfl` or `decide`), without a
compiler-backed decision shortcut.
-/

namespace CertifiedProjections
namespace Interval

variable {p : ℕ}

theorem validCheck_sound {I : Interval p} (h : validCheck I = true) :
    I.Valid := by
  change I.lo ≤ I.hi
  change decide (I.lo ≤ I.hi) = true at h
  exact of_decide_eq_true h

theorem upperLTCheck_sound {I : Interval p} {bound : ℚ}
    (h : upperLTCheck I bound = true) :
    I.upperRat < bound := by
  change decide (I.upperRat < bound) = true at h
  exact of_decide_eq_true h

theorem lowerGTCheck_sound {I : Interval p} {bound : ℚ}
    (h : lowerGTCheck I bound = true) :
    bound < I.lowerRat := by
  change decide (bound < I.lowerRat) = true at h
  exact of_decide_eq_true h

theorem nonnegCheck_sound {I : Interval p} (h : nonnegCheck I = true) :
    0 ≤ I.lo := by
  change decide (0 ≤ I.lo) = true at h
  exact of_decide_eq_true h

/--
Lift a strict rational endpoint comparison to every real number enclosed by
the interval.
-/
theorem lt_of_contains_of_upperLTCheck {I : Interval p} {x : ℝ} {bound : ℚ}
    (hx : I.Contains x) (h : upperLTCheck I bound = true) :
    x < (bound : ℝ) := by
  have hi := upperLTCheck_sound h
  exact hx.2.trans_lt <| by
    rw [← Dyadic.cast_toRat]
    exact_mod_cast hi

/--
Lift a strict rational comparison with the lower endpoint to every real
number enclosed by the interval.
-/
theorem lt_of_lowerGTCheck_of_contains {I : Interval p} {x : ℝ} {bound : ℚ}
    (h : lowerGTCheck I bound = true) (hx : I.Contains x) :
    (bound : ℝ) < x := by
  have hlo := lowerGTCheck_sound h
  have hcast : (bound : ℝ) < Dyadic.toReal p I.lo := by
    rw [← Dyadic.cast_toRat]
    exact_mod_cast hlo
  exact hcast.trans_le hx.1

end Interval
end CertifiedProjections
