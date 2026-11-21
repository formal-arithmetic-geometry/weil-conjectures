/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.BrauerScalarDefectFaithfulForward
import WeilConjectures.FieldTheory.BrauerScalarDefectFaithfulBackward

/-!
# Faithfulness and independence of scalar-defect classes

Source: Stacks Project, Theorem 03R7, homomorphism and injectivity arguments.
-/

@[expose] public section

universe u

namespace Field

/-- Two scalar-defect realizations give the same cohomology class exactly when their
algebras are Brauer equivalent. In particular the class of each algebra is unique.

Source: Stacks Project, Theorem 03R7 (homomorphism and injectivity), and the scalar-defect
construction preceding it. -/
theorem brauerScalarDefect_eq_iff (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y) :
    x = y ↔ IsBrauerEquivalent A B := by
  constructor
  · intro hxy
    exact brauerEquivalent_of_brauerScalarDefect_eq K A B x y hx hy hxy
  · intro hAB
    exact brauerScalarDefect_eq_of_brauerEquivalent K A B x y hx hy hAB

end Field
