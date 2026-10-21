/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.ScalarPullbackComposition
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Counit scalar maps and ordinary étale direct-image composition

Source: Stacks Project, sites-cohomology.tex, Tag 0E46 (remark-compose-base-change),
with Tags 07A6 and 0D6E for the canonical adjunctions and K-injective comparisons
(blueprint: lem-pur-etale-direct-image-scalar-composition).

The coefficient comparison is the existing `scalarMate`, whose transpose is the
scalar/pullback isomorphism followed by scalar extension of the geometric counit.
The compositors below are the universal right-derived comparisons, normalized by
K-injective resolutions, in the direction from composite to iterated direct image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The counit coefficient mate commutes with composition of arbitrary scheme morphisms.
Source: Stacks Project, Tag 0E46 (remark-compose-base-change)
(blueprint: lem-pur-etale-direct-image-scalar-composition).

Proof:
1. The normalized direct-image comparison is adjunction-compatible by
   lem-sfb-ringed-derived-monoidal-comparisons. Thus the composite counit is the
   counit for r after r-pullback of the counit for s. Exact inverse image is the
   constant-ring module pullback by prop-weil-pbc-inverse-image-modules-exact.
2. Apply lem-sf-scalar-pullback-composition: the K-flat-normalized scalar/pullback
   isomorphism for r followed by s is the pasted pair of scalar/pullback isomorphisms.
3. By def-kun-projection-formula-map and lem-weil-pbc-adjunct-counit-identity,
   the transpose of each scalarMate is its scalar/pullback map followed by scalar
   extension of the A-counit.
4. Transport the source along scalar extension of the A-compositor and transpose
   both proposed arrows under the composite B-adjunction. For the composite mate,
   steps 1 and 2 give scalar extension of the r-counit and pulled-back s-counit,
   preceded by the two scalar/pullback comparisons.
5. For the iterated mates, naturality of the s-counit moves the r-mate through it.
6. Substitute the two transpose equations from step 3. Naturality of the r scalar/
   pullback comparison at the s-counit gives precisely the expression in step 4.
   Injectivity of the Hom bijection gives equality; undo the source transport.
All arguments use unbounded K-flat and K-injective models; neither coefficient
flatness nor invertibility of the coefficient mate is used. -/
theorem scalarMate_directImage_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (r : X ⟶ Y) (s : Y ⟶ Z)
    (M : DerivedCategoryModule A X) :
    (scalarMate φ (r ≫ s)).app M ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} B) r) (lowerStar (ModuleCat.{u + 1} B) s)
          (lowerStarComp (ModuleCat.{u + 1} B) r s)).inv.app
            ((scalarExtension φ X).obj M) =
      (scalarExtension φ Z).map
          ((Functor.rightDerivedFunctorCompIso'
            (lowerStar (ModuleCat.{u + 1} A) r) (lowerStar (ModuleCat.{u + 1} A) s)
            (lowerStarComp (ModuleCat.{u + 1} A) r s)).inv.app M) ≫
        (scalarMate φ s).app (R(lowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) s).map ((scalarMate φ r).app M) := by
  sorry

/-- Under the canonical identity direct-image comparisons the coefficient mate is identity.
Source: Stacks Project, Tags 0E46, 07A6 and 0D6E, identity normalization
(blueprint: lem-pur-etale-direct-image-scalar-composition).

Proof (step 7 of the node): the canonical identity pullback compositor is identity
on K-flat representatives, and every object has such a representative by
lem-pc-kflat-resolution. Apply lem-sf-scalar-pullback-composition to two identity
maps. The identity scalar/pullback comparison is idempotent; it is invertible by
def-pur-etale-scalar-pullback-iso, so it is identity. The identity adjunction has
identity counit by lem-sfb-ringed-derived-monoidal-comparisons. The defining transpose
of scalarMate is therefore identity, and the Hom bijection gives the displayed
identity after the two canonical direct-image identifications. -/
theorem scalarMate_directImage_identity
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (M : DerivedCategoryModule A T) :
    (scalarMate φ (𝟙 T)).app M ≫
        (Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} B) T) ≪≫
          (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app ((scalarExtension φ T).obj M) =
      (scalarExtension φ T).map
        ((Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} A) T) ≪≫
          (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app M) := by
  sorry

end AlgebraicGeometry.Etale
