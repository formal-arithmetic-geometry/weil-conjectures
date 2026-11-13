/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.HomComplexRestrictSchemeTransport
import WeilConjectures.AlgebraicGeometry.InternalHomOverEquiv

/-! # Ordinary internal Hom complexes on an open subscheme

## References

* Stacks Project, Tag 08DL
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Ordinary internal Hom commutes with restriction to an open subscheme.
(Stacks, Tag 08DL) -/
theorem homComplex_restrict_scheme {Y : Scheme.{u}} (U : Y.Opens)
    (L M : CochainComplex Y.Modules ℤ) :
    Nonempty (
      ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj
        (homComplex (R := Y.toRingedSpace.sheaf) L M) ≅
      homComplex (R := U.toScheme.toRingedSpace.sheaf)
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj L)
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj M)) := by
  obtain ⟨e, he⟩ := internalHom_overEquiv U
  exact homComplex_restrict_scheme_of_homIso U L M e he

end AlgebraicGeometry
