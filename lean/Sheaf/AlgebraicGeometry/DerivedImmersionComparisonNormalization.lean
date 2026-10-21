/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Sheaf.SixFunctors.OpenTensorNormalizationData

import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.CategoryTheory.ExactDerivedTransformationPasting
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral

/-!
# Restriction normalization of derived immersion comparisons

Source: blueprint main-20261015, proof of `lem-weil-finite-duality-site-comparison`,
second paragraph; Stacks Tags 09AF, 09BM, 09AA, 015F and 0FND
(blueprint: lem-sf-derived-immersion-comparison-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

/-- Open etale restriction is also a left adjoint, hence preserves colimits.
Source: Stacks Tag 03DI; the existing restriction/direct-image adjunction
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
instance derivedImmersionEtaleRestriction_isLeftAdjoint (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).IsLeftAdjoint :=
  (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).isLeftAdjoint

/-- Open pro-etale restriction is also a left adjoint, hence preserves colimits.
Source: Stacks Tag 09AE; the existing restriction/direct-image adjunction
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
instance derivedImmersionProEtaleRestriction_isLeftAdjoint (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionRestriction (ModuleCat.{u + 1} A) j).IsLeftAdjoint :=
  (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).isLeftAdjoint

/-- Termwise canonical pullback comparison in open-restriction form, using the exact
composition identifications. Source: Stacks Tags 09AF and 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
def derivedImmersionOpenPullbackComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openComparisonRestrictionIso A j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Termwise descent of the specified canonical open extension comparison.
Source: Stacks Tags 09AF and 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
def derivedImmersionOpenExtensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
        Functor.mapDerivedCategoryCompIso _ _

/-- The exact derived etale open adjunction, with its localized ordinary unit and counit.
Source: Stacks Tag 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
abbrev derivedImmersionOpenEtaleAdjunction (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)

/-- The exact derived pro-etale open adjunction, localized with the same normalization.
Source: Stacks Tag 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
abbrev derivedImmersionOpenProEtaleAdjunction (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)

/-- The canonical open comparisons respect units and counits on the unbounded derived
categories. The invertible units identify the restricted extension comparison with the
identity. Source: blueprint finite-duality site-comparison proof, paragraph 2;
Stacks Tags 09AF, 0F70 and 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof:
1. Comparison, both restrictions and both extensions by zero are exact. Apply the
exact-functor localization to their canonical sheaf comparisons.
2. The sheaf unit equation is `openComparison_unit_normalization` (Tag 09AF).
3. Transpose C_X(e_M) after the inverse open comparison. Naturality of the pullback
comparison and the etale triangle identity give a_M as its transpose. The inverse
transpose is e'_M after j_!(a_M), giving the sheaf counit equation.
4. Exact derived adjunctions localize these units and counits. Exact transformation
pasting localizes both sheaf equations, with the displayed canonical compositors.
5. The etale open unit is invertible, as is its termwise inverse after localization.
The unit equation then makes the pro-etale unit at C_U L invertible. Cancelling the
units says precisely that the restriction of o_j is the identity. The canonical
pullback comparisons carry their identity and composition identifications through
localization; the same argument covers identity and empty immersions. -/
theorem derivedImmersionOpen_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.map
          ((derivedImmersionOpenEtaleAdjunction A j).unit.app L) ≫
        (derivedImmersionOpenPullbackComparison A j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L) ≫
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
          ((derivedImmersionOpenExtensionComparison A j).hom.app L) =
      (derivedImmersionOpenProEtaleAdjunction A j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L)) ∧
    (∀ M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (derivedImmersionOpenExtensionComparison A j).hom.app
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
          ((derivedImmersionOpenPullbackComparison A j).hom.app M) ≫
        (derivedImmersionOpenProEtaleAdjunction A j).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((derivedImmersionOpenEtaleAdjunction A j).counit.app M)) ∧
    (∀ L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
      IsIso ((derivedImmersionOpenEtaleAdjunction A j).unit.app L) ∧
      IsIso ((derivedImmersionOpenProEtaleAdjunction A j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L))) := by
  sorry

/-- Etale closed direct image is exact; left exactness is already supplied by its
right-adjoint structure. Source: Stacks Tags 04CA and 08M3
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: identify the etale topos of the closed subscheme with the closed complement
topos. Its direct image on modules is exact and fully faithful, with invertible
restriction counit, as in lem-trf-oriented-closed-base-localization. -/
@[instance] theorem derivedImmersionClosedEtale_exact (A : Type (u + 1)) [CommRing A]
    [Finite A] {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h] :
    PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) h) := by
  sorry

/-- Pro-etale closed direct image is exact over a Noetherian target; its left
exactness is the right-adjoint structure. Source: Stacks Tag 09BM
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: the complement open immersion is quasi-compact: every open in a Noetherian
scheme is quasi-compact. Apply lem-exc-proetale-closed-exact to this complement.
No constructibility hypothesis is used. -/
@[instance] theorem derivedImmersionClosedProEtale_exact (A : Type (u + 1)) [CommRing A]
    [Finite A] {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h] :
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) h) := by
  sorry

/-- The ordinary closed comparison is the specified counit transpose, not an
independently chosen isomorphism. Source: Stacks Tag 0B65
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: the direct-image comparison is the double mate of the sectionwise comparison
of direct images. The iterated-mate identity identifies it with the mate of the
canonical pullback comparison. Applying the inverse-transpose counit formula gives
exactly the asserted component formula. -/
theorem derivedImmersionClosed_sheaf_transpose (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)).app F =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ _)
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) h).hom.app
            ((Etale.lowerStar (ModuleCat.{u + 1} A) h).obj F) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Z).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).counit.app F)) := by
  sorry

/-- Termwise descent on D+ of the ordinary closed counit mate. The sheaf mate is
invertible for this qcqs morphism, so its descent uses the standard natural-iso API.
Source: Stacks Tags 099R, 015F and 0B65
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
def derivedImmersionClosedTermwiseComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h] :
    (Etale.lowerStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus :=
  letI := isIso_lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (asIso (lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A))) ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _

/-- The specified derived closed mate equals the termwise sheaf mate under the
canonical exact-functor identifications; its counit equation has invertible counits,
so restriction identifies it with the identity of C_Z L.
Source: blueprint finite-duality site-comparison proof, paragraph 2;
Stacks Tags 015F, 0FND, 09AA and 0B65
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof:
1. The two closed direct images are exact by the preceding exactness statements.
Their universal right-derived comparisons with termwise localization are invertible.
2. The fraction formula of lem-pc-pre-derived-adjoint-functors-general, at identity
quasi-isomorphisms, identifies the derived transpose of Q(f) with Q(f-sharp).
The inverse images of other quasi-isomorphisms give the same formula on all fractions.
Thus the derived closed counits are the localized ordinary counits.
3. Localize the ordinary transpose equation by exact transformation pasting. It gives
the counit equation for the termwise mate. The specified derived mate has the same
transpose by lem-weil-pbc-comparison-direct-image-canonical-mate. Injectivity of the
adjunction Hom bijection identifies these actual maps, giving the first equality.
4. Both ordinary closed counits are invertible by the closed-complement description
and lem-exc-proetale-closed-fully-faithful. Their termwise inverses localize, giving
invertibility of the derived counits. Cancelling them in the second equality identifies
the restricted mate with the identity. All comparisons use the canonical compositors,
which localize their identity and composition equations, including empty immersions. -/
theorem derivedImmersionClosed_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h]
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((fixedComparisonDirectImageMatePlus A h).app L ≫
      (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.map
          ((Etale.lowerStar (ModuleCat.{u + 1} A) h
            ).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app L) ≫
        (derivedImmersionClosedTermwiseComparison A h).hom.app L) ∧
    ((fixedComparisonPullbackPlus A h).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) h).obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus A h).app L) ≫
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) h).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} A) h).counit.app L)) ∧
    IsIso ((Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} A) h).counit.app L) ∧
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) h).counit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale
