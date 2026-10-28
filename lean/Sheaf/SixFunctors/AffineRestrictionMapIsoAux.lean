/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.FiniteDualizingData

/-! # Invertibility of the finite dualizing comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The global finite dualizing comparison is invertible.

Source: the closed-chart descent and affine-space comparison in
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md`, paragraphs 1--3 (blueprint:
`affine-restriction-map-iso`).  The proof first applies the proper/open
coefficient comparison to the compactification of `X`, then identifies the
resulting mate on each affine chart with the affine-space comparison after a
closed-chart embedding.  Both component comparisons are isomorphisms, and
the jointly-surjective affine cover reflects isomorphisms of derived etale
objects.  Thus the specified counit-defined global mate is an isomorphism;
the argument also covers an empty affine chart because its derived category
is zero. -/
theorem finiteDualizing_etaleComparison_isIso_for_factorization (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m) :
    IsIso (finiteDualizingEtaleComparison l E D X h) := by
  sorry

end WeilConjectures
