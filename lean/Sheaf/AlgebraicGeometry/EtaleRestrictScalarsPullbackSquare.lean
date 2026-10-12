/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons

/-! # Coefficient compatibility of derived pullback squares -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Coefficient restriction commutes with the comparison of the two composite
inverse images attached to a commutative square.

Source: Stacks Project, Remark 21.19.3, Tag 07A7, and the composition of inverse images
in the definition of the exchange map.
Proof: for composable morphisms, compare both coefficient transports of their
composite inverse image. Inverse images are left adjoints to the sectionwise direct
images; the coefficient comparison is obtained from the common direct-image/coextension
composite by uniqueness of left adjoints. Uniqueness is transitive and compatible with
composition of adjunctions. Thus the coefficient comparison for a composite equals
the composite of the two coefficient comparisons, with the inverse-image composition
isomorphisms inserted. Apply this once to h followed by p and once to e followed by g.
The equality h ≫ p = e ≫ g identifies the composite comparisons. Composing the first
identity with the inverse of the second gives the asserted square. Apply exact
derivation: mapDerivedCategoryPlusNatIso preserves composition and its composition
isomorphisms are natural, so the same identity holds in D⁺. No direct-image derived
functor or adjunction unit/counit occurs in this assertion.
(blueprint: lem-sbc-restrict-scalars-pullback-square-comparison) -/
theorem pullbackSquareComparison_restrictScalars
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : CommSq e h g p)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (D+((h)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarRestrictScalarsIso φ p).hom.app L) ≫
      (derivedUpperStarRestrictScalarsIso φ h).hom.app
        ((D+((p)^*[ModuleCat.{u + 1} Λ'])).obj L) ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((pullbackSquareComparison (ModuleCat.{u + 1} Λ') sq).hom.app L) =
    (pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (D+((e)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarRestrictScalarsIso φ g).hom.app L) ≫
      (derivedUpperStarRestrictScalarsIso φ e).hom.app
        ((D+((g)^*[ModuleCat.{u + 1} Λ'])).obj L) := by sorry

end AlgebraicGeometry.Etale
