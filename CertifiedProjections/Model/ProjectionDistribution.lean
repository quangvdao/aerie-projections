/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CertifiedProjections.Model.Distributions.SparseRademacher

/-!
# Projection distributions

This module gives the public vocabulary for the matrix distributions used by
CertifiedProjections. A descriptor determines the exact PMF of one row and of a matrix.
The sparse Rademacher case samples each entry independently, with masses `1/4`,
`1/2`, and `1/4` at `-1`, `0`, and `1`.
-/

namespace CertifiedProjections

/-- A supported distribution for sampling projection rows and matrices. -/
inductive ProjectionDistribution
  | sparseRademacher
deriving DecidableEq, Repr

namespace ProjectionDistribution

/-- The exact finite PMF of one projection row in dimension `d`. In the
sparse Rademacher case, its `d` entries are mutually independent. -/
noncomputable def rowPMF (distribution : ProjectionDistribution) (d : ℕ) : PMF (Fin d → ℤ) :=
  match distribution with
  | .sparseRademacher => sparseRademacherRow d

/-- The exact finite PMF of a `rows`-by-`d` projection matrix. In the
sparse Rademacher case, all entries are mutually independent. -/
noncomputable def matrixPMF (distribution : ProjectionDistribution) (rows d : ℕ) :
    PMF (Fin rows → Fin d → ℤ) :=
  match distribution with
  | .sparseRademacher => sparseRademacherMatrix rows d

@[simp]
theorem rowPMF_sparseRademacher (d : ℕ) :
    rowPMF .sparseRademacher d = sparseRademacherRow d :=
  rfl

@[simp]
theorem matrixPMF_sparseRademacher (rows d : ℕ) :
    matrixPMF .sparseRademacher rows d =
      sparseRademacherMatrix rows d :=
  rfl

end ProjectionDistribution
end CertifiedProjections
