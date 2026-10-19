/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.SfFiniteOpenExtensionBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.FixSiteOpenExchange
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-! # Compactified site comparison and open restriction

Source: Stacks Project, proetale.tex, Tags 09A6 and 09AF; canonical mate pasting
(blueprint: lem-amb-compact-support-site-comparison-open).
The coefficient category is the canonical fixed-scalar presentation of ordinary
constant-ring modules. All operations are ordinary and are restricted to D+.

## Main definitions and statements

- `compactSupportEtaleExchangePlus`, `compactSupportProEtaleExchangePlus`: the two actual
  proper-exchange followed by inverse open-extension-exchange maps.
- `compactSupportSiteComparison_open`: their compatibility with the canonical comparison.
- `compactSupportSiteComparison_open_counits`: the direct-image and evaluation normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The etale compactified exchange: proper derived mate, then inverse open-extension mate.
Source: Stacks Tags 03S6 and 09A6
(blueprint: lem-amb-compact-support-site-comparison-open). -/
def compactSupportEtaleExchangePlus (A : Type u) [CommRing A] [Finite A]
    {X' X S' S : Scheme.{u}} {v : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {u : S' ⟶ S}
    (sq : IsPullback v f' f u) (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) u).mapDerivedCategoryPlus ⟶
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) v).mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (c.ofIsPullback sq) :=
  letI := Etale.isIso_openImmersionLowerShriekBaseChangeMap
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (c.isPullback_i_ofIsPullback sq)
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (asIso (Etale.openImmersionLowerShriekBaseChangeMap
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              (c.isPullback_i_ofIsPullback sq).toCommSq)).symm ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _).hom _ ≫
    (Functor.associator _ _ _).hom

/-- The pro-etale compactified exchange uses the same two mate constructions.
The direct-image exchange is the mate of the canonical termwise inverse-image square;
the open factor is the inverse of the recorded extension-by-zero conjugate.
Source: Stacks Tags 09A6, 09AF and 04J0
(blueprint: lem-amb-compact-support-site-comparison-open). -/
def compactSupportProEtaleExchangePlus (A : Type u) [CommRing A] [Finite A]
    {X' X S' S : Scheme.{u}} {v : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {u : S' ⟶ S}
    (sq : IsPullback v f' f u) (c : Compactification f) :
    rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) u).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) v).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (c.ofIsPullback sq) :=
  letI := sfFixedOpenExtensionBaseChange_isIso A (c.isPullback_i_ofIsPullback sq)
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (mateEquiv
        (derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g)
        (derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (c.ofIsPullback sq).g)
        ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryPlusNatIso
            (upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              (c.isPullback_g_ofIsPullback sq).w) ≪≫
          Functor.mapDerivedCategoryPlusCompIso _ _).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (asIso (sfFixedOpenExtensionBaseChange A
            (c.isPullback_i_ofIsPullback sq).toCommSq)).symm ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _).hom _ ≫
    (Functor.associator _ _ _).hom

/-- The canonical compactification comparison commutes with open restriction, with
both inverse-image comparisons displayed. Its isomorphism assertion is carried by
`compactSupportSiteComparisonPlus`; equality is between components of natural maps,
so the statement is natural in the entire bounded-below complex.
Source: Stacks proetale.tex, Tags 09A6 and 09AF, canonical open-restriction pasting
(blueprint: lem-amb-compact-support-site-comparison-open).

Proof (the node's seven steps):
1. Properness of c.g gives qcqs; base change preserves it. Use
lem-weil-pbc-comparison-pullback to identify the inverse-image composites.
2. Exact open extension, comparison and inverse image preserve D+ by
lem-weil-pbc-exact-functor-bounded-below. Use the specified adjunction-normalized
open comparison of lem-fix-site-open-exchange, not an arbitrary isomorphism.
3. J is the proper counit mate followed by direct image of the open comparison.
lem-weil-pbc-comparison-direct-image-canonical-mate makes the first factor invertible;
the second is an isomorphism. This is exactly compactSupportSiteComparisonPlus.
4. Apply lem-weil-pbc-transport-identifies-exchange to c.g and its open base change:
the two proper exchanges intertwine the actual proper comparison mates.
5. Apply lem-fix-site-open-exchange to the open square. Its equation intertwines
the actual inverse extension-by-zero exchanges and the two open site comparisons.
6. Expand both compactified exchanges. Naturality of the proper exchange moves
the open site comparison through it. Substitute step 5 and then step 4; naturality
of the base-changed proper comparison moves the etale open exchange through it.
Functoriality combines the resulting two factors to give the displayed right side.
7. The proper mate's counit equation gives its normalization. For the open factor,
transpose its inverse under the open adjunction. Naturality of the pullback comparison
and the etale triangle identity identify the transpose with the pullback comparison.
The pro-etale triangle identity identifies the same transpose for the evaluation
counit composite. Injectivity of the Hom adjunction proves equality. This applies
also to the restricted compactification. All maps used above are natural. -/
theorem compactSupportSiteComparison_open (A : Type u) [CommRing A] [Finite A]
    {X' X S' S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    {v : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {u : S' ⟶ S}
    [IsOpenImmersion u] (sq : IsPullback v f' f u) (c : Compactification f)
    [IsNoetherian c.Z]
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) u).mapDerivedCategoryPlus.map
        ((compactSupportSiteComparisonPlus (ULift.{u + 1, u} A) c).hom.app L) ≫
      (compactSupportProEtaleExchangePlus A sq c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategoryPlus.obj
          L) ≫
      (rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (c.ofIsPullback sq)).map
          ((fixedComparisonPullbackPlus (ULift.{u + 1, u} A) v).inv.app L) =
    (fixedComparisonPullbackPlus (ULift.{u + 1, u} A) u).inv.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) S').mapDerivedCategoryPlus.map
          ((compactSupportEtaleExchangePlus A sq c).app L) ≫
      (compactSupportSiteComparisonPlus (ULift.{u + 1, u} A) (c.ofIsPullback sq)).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) v).mapDerivedCategoryPlus.obj
          L) := by
  sorry

/-- The site factors used in J preserve the actual proper and open-evaluation counits.
The same assertion for the restricted compactification is obtained by applying this
statement to c.ofIsPullback sq. Source: Stacks Tags 09A6 and 09AF
(blueprint: lem-amb-compact-support-site-comparison-open).

Proof: step 7 of the node. The proper equation is the defining counit-mate identity
of lem-weil-pbc-comparison-direct-image-canonical-mate. For the open equation,
transpose under the open adjunction: the inverse comparison is normalized by the
etale unit and pullback comparison as in lem-fix-site-open-exchange. Naturality and
the etale triangle identity make its transpose the pullback comparison. The
pro-etale triangle identity gives the same transpose for the evaluation composite.
The adjunction Hom bijection is injective, proving the displayed equation. -/
theorem compactSupportSiteComparison_open_counits
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    {f : X ⟶ S} (c : Compactification f) [IsNoetherian c.Z] :
    (∀ K : DerivedCategory.Plus (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (fixedComparisonPullbackPlus A c.g).hom.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) c.g).obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) c.g).mapDerivedCategoryPlus.map
          ((fixedComparisonDirectImageMatePlus A c.g).app K) ≫
        (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) c.g).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus.obj K) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) c.g).counit.app K)) ∧
    (∀ B : DerivedCategory.Plus (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus.map
          ((Etale.openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlusAdjunction.counit.app B) =
        (properOpenSiteExtensionIso A c.i).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj B) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus A c.i).hom.app B) ≫
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlusAdjunction.counit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus.obj B)) := by
  sorry

end AlgebraicGeometry.ProEtale
