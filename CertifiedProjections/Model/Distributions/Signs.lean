/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Matrix.Basic

/-!
# Sign seeds for projection distributions

Boolean seeds give finite, computable sample spaces for sign-valued projection
rows and matrices.
-/

namespace CertifiedProjections

/-- One independent bit for each entry of a sign row. -/
abbrev SignRowSeed (d : ℕ) := Fin d → Bool

/-- One independent bit for each entry of a sign matrix. -/
abbrev SignSeed (rows d : ℕ) := Fin rows → Fin d → Bool

/-- Interpret a bit as a Rademacher sign. -/
def signBit : Bool → ℤ
  | false => -1
  | true => 1

/-- Interpret a sign-row seed as an integer row. -/
def signRow {d : ℕ} (seed : SignRowSeed d) : Fin d → ℤ :=
  fun i => signBit (seed i)

/-- Interpret a sign-matrix seed as an integer matrix. -/
def signMatrix {rows d : ℕ} (seed : SignSeed rows d) :
    Fin rows → Fin d → ℤ :=
  fun j => signRow (seed j)

end CertifiedProjections
