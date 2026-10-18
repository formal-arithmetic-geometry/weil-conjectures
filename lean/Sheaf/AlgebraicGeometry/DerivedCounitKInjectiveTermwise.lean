/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Derived counit on a K-injective representative

Source: `literature/stacks-project/derived.tex`, Tags 0DVC and 09T5
(blueprint: lem-asd-derived-counit-k-injective-termwise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/--
Source: Stacks Project, `derived.tex`, Tags 0DVC and 09T5, with Tag 070K for the
K-injective computation and Tag 015F for the exact inverse image.

(blueprint: lem-asd-derived-counit-k-injective-termwise).

Let `R` be a commutative ring and `f : X ⟶ Y` a morphism of schemes.  The derived
adjunction between the exact inverse image and the right derived direct image has,
at a K-injective complex `I` on `X`, the ordinary termwise sheaf counit.  The
five displayed factors below are respectively the K-injective comparison, the
canonical quotient comparison for the exact inverse image, the exact-functor
factorization, the ordinary counit on homotopy categories, and the quotient
comparison back to the derived category.  Thus the displayed equality is exactly
the representative assertion in the node, including the canonical comparison
`u⁻¹ Q (u_* I) ≅ Q (u⁻¹ u_* I)`.

The proof is the standard derived-adjunction calculation.  Exactness of inverse
image gives its termwise derived functor and the quotient comparison.  The
K-injective comparison identifies `R f_* (Q I)` with `Q (f_* I)`.  The homotopy
adjunction has counit the componentwise sheaf counit; applying the quotient and
composing the canonical comparisons gives the displayed derived counit.  This
is the three-step proof recorded in the DAG node, using
`prop-weil-pbc-inverse-image-modules-exact`,
`def-weil-pbc-derived-inverse-image`,
`lem-weil-pbc-exact-functor-derived-functor`,
`lem-weil-pbc-kinjective-total-derived`, and
`def-kun-unbounded-exchange`.
-/
theorem derivedCounitKInjectiveTermwise
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R] (f : X ⟶ Y)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat R)) ℤ)
    [I.IsKInjective] :
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat R) f).counit.app
        (DerivedCategory.Q.obj I) =
      (D((f)^*[ModuleCat R])).map
          ((f)_*[ModuleCat R].rightDerivedFunctorObjQIso I).hom ≫
        D((f)^*[ModuleCat R]).map
          ((DerivedCategory.quotientCompQhIso
              (Sheaf Y.smallEtaleTopology (ModuleCat R))).inv.app
            (((f)_*[ModuleCat R].mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        (f)^*[ModuleCat R].mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient
              (Sheaf Y.smallEtaleTopology (ModuleCat R)) (ComplexShape.up ℤ)).obj
            (((f)_*[ModuleCat R].mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategory (ComplexShape.up ℤ)
              (upperStarLowerStarAdjunction (ModuleCat R) f)).counit.app
            ((HomotopyCategory.quotient
                (Sheaf X.smallEtaleTopology (ModuleCat R)) (ComplexShape.up ℤ)).obj I)) ≫
        (DerivedCategory.quotientCompQhIso
            (Sheaf X.smallEtaleTopology (ModuleCat R))).hom.app I := by
  sorry

end AlgebraicGeometry.Etale
