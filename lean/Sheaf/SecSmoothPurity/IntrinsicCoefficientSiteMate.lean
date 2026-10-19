/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Sheaf.Paper.EtaleProEtaleCoefficientTransport
public import Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange
public import Sheaf.Paper.PurEtaleScalarMateProjection
import Sheaf.SecSmoothPurity.RealizationRestrictionDirectImage
import Sheaf.SecSmoothPurity.EtaleScalarSheafPullbackMate

/-! # Intrinsic presentation of the coefficient/site mate square

Source: blueprint main-20261015, scalar-six direct-image proof, finite rings paragraph,
Steps 2--5 of lem-sfb-etale-proetale-scalar-mate; Stacks Tags 07A4 and 09A6.
(blueprint: lem-sp-intrinsic-coefficient-site-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
open CoefficientCompatibility

/-- The scalar presentation square for exact etale comparison and intrinsic realization.
It is determined by the section-normalized restriction comparison and scalar adjunctions.
Source: Stacks Tags 00YV, 06YY and 07A4
(blueprint: lem-sp-intrinsic-coefficient-site-mate). -/
def intrinsicCoefficientSiteScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    etaleOriginOpenComparison A T ⋙ scalarExtensionFunctor φ T ≅
      Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙
        etaleOriginOpenComparison B T :=
  isoWhiskerLeft
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory
    (scalarPresentation φ T) ≪≫
    isoWhiskerRight
      (pbcComparisonReduction T (RingHom.ulift.{u + 1, u + 1, u, u} φ))
      (sfIntrinsicDerivedEquivalence T B).functor

/-- The canonical site/direct-image mate in intrinsic constant-ring coordinates.
The presentation isomorphism uses the unit-normalized geometric adjunction coordinates.
Source: Stacks Tag 09A6
(blueprint: lem-sp-intrinsic-coefficient-site-mate). -/
def intrinsicCoefficientSiteDirectImageComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
        etaleOriginOpenComparison A Y ⟶
      etaleOriginOpenComparison A X ⋙ directImageConstantPush A f :=
  whiskerRight (directImageComparisonAmbient (ULift.{u + 1, u} A) f) _ ≫
    whiskerLeft _ (directImagePresentation A f).inv

/-- The coefficient/site mate square in intrinsic constant-ring coordinates.
No scalar mate is inverted, and no boundedness or properness is needed for this equality.
Source: blueprint main-20261015, scalar-six direct-image proof, finite rings paragraph,
Steps 2--5 of lem-sfb-etale-proetale-scalar-mate; Stacks Tags 07A4 and 09A6.
(blueprint: lem-sp-intrinsic-coefficient-site-mate).

Proof:
1. Realization is the sheafification of the constant-module presheaf. Its canonical
   restriction comparison and its direct-image comparison preserve realization-unit
   sections. On a section arising from this unit, restriction followed by direct image
   in either order is the identical section on the base-changed site object. The unit
   is locally surjective (indeed sectionwise bijective for a finite coefficient ring),
   so these equalities prove realizationRestrictionDirectImage, the ordinary square.
2. The ordinary geometric coordinate change is fixed by its tensor-unit equation.
   Transpose the square of step 1 under the two geometric adjunctions. Uniqueness of
   adjoints identifies the result with the canonical restriction/pullback square.
   Deriving exact restriction and pullback carries this equality to complexes and then
   to the localization, with the canonical composition factor isomorphisms.
3. The proved scalarSheafPullbackIso_inverseMate identifies the ordinary inverse
   scalar mate. Transpose under the two scalar adjunctions. Their unit equations identify the
   scalar presentation with scalarPresentation. On a cochain representative, apply
   exact restriction to the scalar representative map. Its adjoint transpose is
   the ordinary scalar unit followed by the inverse exact-restriction factor map.
   The geometric representative is the exact-pullback factor map preceded by the
   derived/exact-pullback comparison. Naturality of these factor maps reduces the
   normalization equation to the ordinary scalar-unit mate equation of
   scalarSheafPullbackIso_inverseMate. This identifies the etale inverse scalar mate
   with Etale.scalarPullbackIso, by its uniqueness on K-flat representatives. The
   same restriction and unit calculation in intrinsic modules identifies the other
   inverse scalar mate with directImageScalarPullbackIso. The universal derived
   counits and K-flat resolutions identify these natural transformations on all objects.
4. Paste the exact etale/pro-etale pullback square into step 3, as in the coefficient/
   site cube in lem-sfb-etale-proetale-scalar-mate. Both routes preserve every pure
   tensor, so the square commutes before taking a geometric mate.
5. Transpose the two routes under the B-geometric adjunction. Naturality moves the
   scalar presentation past the A-counit; the mate equation replaces the A-site mate
   followed by that counit by the exact pullback square and the etale A-counit. Use
   the equality in step 4 and then the B-site mate equation. Both transposes agree.
   Injectivity of the adjunction Hom equivalence gives the displayed equality.
   Associators and the two realization presentation maps give exactly its boundaries.
   All equalities are natural transformations, so they hold on unbounded inputs as
   well as on the zero ring and empty schemes. -/
theorem intrinsicCoefficientSiteMate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    (scalarExtensionFunctor φ Y).map
        ((intrinsicCoefficientSiteDirectImageComparison A f).app J) ≫
      (directImageScalarComparison φ f).app ((etaleOriginOpenComparison A X).obj J) ≫
      (directImageConstantPush B f).map ((intrinsicCoefficientSiteScalarIso φ X).hom.app J) =
    (intrinsicCoefficientSiteScalarIso φ Y).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj J) ≫
      (etaleOriginOpenComparison B Y).map
        ((Etale.scalarMate (RingHom.ulift.{u + 1, u + 1, u, u} φ) f).app J) ≫
      (intrinsicCoefficientSiteDirectImageComparison B f).app
        ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj J) := by
  sorry


end AlgebraicGeometry.ProEtale
