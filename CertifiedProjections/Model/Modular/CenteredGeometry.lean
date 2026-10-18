/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Modular.Centered

/-!
# Elementary centered-modulus geometry

Endpoint-independent deterministic inequalities for centered modular
reduction.
-/

namespace CertifiedProjections

/--
If centered reduction changes an integer, the modulus is at most the sum of
the absolute values of the integer and its centered representative.
-/
theorem centeredMod_modulus_le_natAbs_add_of_ne
    {q : ℕ} {z : ℤ} (hne : z ≠ centeredMod q z) :
    q ≤ z.natAbs + (centeredMod q z).natAbs := by
  have hcast :
      ((centeredMod q z : ℤ) : ZMod q) = (z : ZMod q) :=
    centeredMod_intCast q z
  have hdvd : (q : ℤ) ∣ z - centeredMod q z := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      (centeredMod q z) z q).mp hcast
  have hsub : z - centeredMod q z ≠ 0 := sub_ne_zero.mpr hne
  have hqle : q ≤ (z - centeredMod q z).natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hsub
  exact hqle.trans (Int.natAbs_sub_le z (centeredMod q z))

end CertifiedProjections
