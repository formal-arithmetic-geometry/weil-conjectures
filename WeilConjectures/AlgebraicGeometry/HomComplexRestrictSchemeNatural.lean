/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.HomComplexRestrictSchemeNaturalComponents

/-! # Naturality of restriction of the ordinary internal Hom complex

## References

* Stacks Project, Tag 08DL
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Restriction of ordinary internal Hom is natural in the second complex.
(Stacks, Tag 08DL) -/
theorem homComplex_restrict_scheme_natural {Y : Scheme.{u}} (U : Y.Opens)
    (L : CochainComplex Y.Modules ℤ) :
    Nonempty (
      (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj (op L) ⋙
          (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ) ≅
      (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ) ⋙
        (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj
          (op (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj
            L))) := by
  obtain ⟨e, he⟩ := homComplex_restrict_scheme_natural_components U L
  exact ⟨CategoryTheory.NatIso.ofComponents e (by
    intro M N f
    exact he f)⟩


end AlgebraicGeometry
