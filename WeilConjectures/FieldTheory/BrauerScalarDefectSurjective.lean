/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.CrossedProductRealization

/-!
# Crossed-product realization of continuous degree-two classes

Source: Stacks Project, Theorem 03R7, surjectivity argument, and Section 0DVG.
-/

@[expose] public section

universe u

namespace Field

/-- Every continuous degree-two Galois class is realized by matrix scalar defects
of a central simple algebra.

Source: Stacks Project, Theorem 03R7, surjectivity argument. -/
theorem exists_csa_brauerScalarDefect (K : Type u) [Field K] (x : GaloisUnitsH2 K) :
    ∃ A : CSA.{u, u} K, HasBrauerScalarDefect K A x := by
  obtain ⟨A, n, hn, e, b, hb, z, hz, hdesc, hdefect⟩ :=
    exists_crossedProduct_realization_data K x
  exact ⟨A, n, hn, e, b, hb, z, hz, hdesc, hdefect⟩

end Field
