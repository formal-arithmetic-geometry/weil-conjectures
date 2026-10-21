/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Normalization of the support scalar mate as a constant-coefficient projection

Source: Stacks Project, Tags 0GL6, 07A6 and 07A7. The comparison is between the
published restriction square and the published counit-defined projection map.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Forgetting the target scalar action and using the fixed-coefficient realization
identifies the canonical support scalar mate with the proper projection map on the
open extension of the input, at the constant source module underlying the target ring.
The statement concerns the actual maps, through an isomorphism in the arrow category;
it makes no claim that either arrow is invertible and assumes no ambient right adjoint.
Source: Stacks Project, Tags 0GL6, 07A6 and 07A7
(blueprint: lem-exc-support-scalar-projection-normalization).

Proof: first use uniqueness of left adjoints to compare the supplied scalar extensions
with K-flat tensor extension. After restriction of scalars, the balancing map identifies
extension of a K-flat complex P with P tensor the constant A-module B. This identification
is natural on complexes and descends through the quasi-isomorphism localization. The
realization equivalence carries this balancing map to the fixed-scalar tensor product:
on a pure tensor its two descriptions send x tensor b to the same section x tensor b.
For the proper part of the restriction square, compute on K-injective representatives.
Its prescribed sectionwise identity identifies the transpose of the scalar mate with
the geometric counit tensored with B. Under the inverse-image tensor comparison this is
exactly the transpose defining the proper projection map. Injectivity of the geometric
adjunction's Hom equivalence identifies these maps. For the open part, the published
restriction square is the unit mate of open restriction. Transposition identifies its
scalar mate with the inverse open projection isomorphism. Paste the two comparisons;
the inverse open projection and the realization comparisons are isomorphisms, producing
an isomorphism of the displayed arrows. The triangle identities cancel all inserted
units and counits. No resolution of the coefficient module is truncated, so neither
flatness of B over A nor boundedness of the input is required. -/
theorem supportScalarMate_projection_arrowIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (LX : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory X B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aX : LX ⊣ (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (K : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty
      (Arrow.mk
        (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
            (sfIntrinsicDerivedEquivalence Y A).inverse).map
          (((mateEquiv aX aY).symm
            (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans.app
              ((sfIntrinsicDerivedEquivalence X A).functor.obj K))) ≅
        Arrow.mk
          (((ProEtale.rightDerivedLowerStarProjectionMap
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).app
              ((ProEtale.openImmersionLowerShriek
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K)).app
            ((constantSheaf (ProEt.topology Y)
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
                  (ModuleCat.of (ULift.{u + 1, u} B) (ULift.{u + 1, u} B))))))) := by
  sorry

end WeilConjectures
