/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.IdentityOpenDerivedRestriction
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Resolution and adjunction normalization over an identity open

Source: Stacks Project, sites-cohomology.tex, Tags 0D6G and 08FI; derived.tex,
Tags 08BJ, 015F, 070Y and 09T5
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization).

The restriction maps are the existing canonical mates. Pullback is derived termwise;
the adjunction is the specified total derived adjunction transported through the canonical
exact-pullback identification. The localized comparison unit uses the existing UnitQ.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The inverse composition comparison `i^* h^* ≅ j^*`, transported along `hi = j`.
Source: the composition convention in the node and Stacks 09T5
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenPullbackComparison {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (w : i ≫ h = j) :
    upperStar Λ h ⋙ upperStar Λ i ≅ upperStar Λ j :=
  (upperStarComp Λ i h).symm ≪≫ upperStarCongr Λ w

/-- The termwise derived comparison `a_h` with its canonical localization identifications.
Source: Stacks 015F and the composition convention
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenDerivedPullbackComparison {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (w : i ≫ h = j) :
    (upperStar Λ h).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory ≅
      (upperStar Λ j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (upperStar Λ h) (upperStar Λ i)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (identityOpenPullbackComparison Λ j i h w)

/-- The specified derived adjunction, expressed with the exact termwise pullback.
This transports the published adjunction, including its actual unit and counit.
Source: Stacks 09T5 and sk-def-sfb-module-derived-pushpull
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenTermwiseDerivedAdjunction {D Z : Scheme.{u}} (h : D ⟶ Z) :
    (upperStar Λ h).mapDerivedCategory ⊣ (lowerStar Λ h).rightDerivedFunctor :=
  (derivedUpperStarLowerStarAdjunction Λ h).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ h)

/-- The comparison unit on complexes, obtained from the published right-derived unit.
Source: Stacks 070Y, localization of the comparison unit
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenRightDerivedUnit {D Z : Scheme.{u}} (h : D ⟶ Z) :
    (lowerStar Λ h).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (lowerStar Λ h).rightDerivedFunctor where
  app P := (lowerStar Λ h).rightDerivedFunctorUnitQ P
  naturality _ _ s := (lowerStar Λ h).rightDerivedFunctorUnitQ_naturality s

/-- The localized comparison unit for `j^* Rh_*`, with the exact-functor factorization.
Source: Stacks 015F and 070Y
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenLocalizedDerivedUnit {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (h : D ⟶ Z) :
    (lowerStar Λ h).mapHomologicalComplex (.up ℤ) ⋙
        (upperStar Λ j).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (lowerStar Λ h).rightDerivedFunctor ⋙
        (upperStar Λ j).mapDerivedCategory :=
  Functor.whiskerLeft ((lowerStar Λ h).mapHomologicalComplex (.up ℤ))
      (upperStar Λ j).mapDerivedCategoryFactors.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (identityOpenRightDerivedUnit Λ h)
      (upperStar Λ j).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- Resolution, comparison-unit and actual derived-adjunction normalization at an identity
open locus. Source: Stacks 0D6G, 08FI, 08BJ, 015F, 070Y and 09T5
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization).

Proof plan (the six steps of the node):
1. Transport to the section-ring module model using
lem-sfb-internal-module-operations-transport. The exact equivalence and its inverse preserve
acyclicity; the Hom and homotopy bijections therefore preserve and reflect K-injectivity.
Use prop-pur-kinjective-resolutions-exist on the small ringed site.
2. Pullbacks are exact by det-prop-sfb-module-pullback-exact-main and descend termwise by
lem-weil-pbc-exact-functor-derived-factorization. Open restriction preserves K-injectives
because its left adjoint is exact (sk-def-sfb-module-lower-shriek and
lem-weil-pbc-right-adjoint-preserves-kinjective). No other inverse image is used here.
3. The specified identity locus makes i a quasi-compact base change of j
(lem-pc-quasi-compact-base-change). Apply lem-sfb-identity-open-derived-restriction.
For a resolution s:P→I, naturality of r and its normalization on I give the resolution
formula below after inverting Q(i^*s); the derived evaluation is Rh_*(Qs) followed by
rightDerivedFunctorObjQIso I.
4. Naturality of the comparison unit gives d_s γ_P = Q(h_*s). Substitute in step 3,
use the termwise naturality of c, and cancel Q(i^*s). This proves the γ formula for every P.
5. The comparison c identifies j^*h_* with the exact functor i^*. The localization universal
property (lem-weil-pbc-localization-universal-property) makes its descent a total right
derived pair. Step 4 transports that universal property through the already canonical r.
6. Apply lem-kun-derived-adjoint-square-comparison with L=h^*, R=h_*, V=i^*, W=j^*,
and the identity adjunction on the open. Its underived compatibility is precisely hc.
Steps 4--5 identify its canonical comparison with r. The two equations of that theorem
give the displayed unit and counit equations for the specified derived adjunction.
-/
theorem identity_open_derived_adjunction_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    {U D Z : Scheme.{u}} [U.Over (Spec (.of k))] [D.Over (Spec (.of k))]
    [Z.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (D ↘ Spec (.of k))] [LocallyOfFiniteType (D ↘ Spec (.of k))]
    [QuasiCompact (D ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z)
    [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))] [h.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    (w : i ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range i)
    (hc : ∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ Z))
      (N : Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ D)) (t : (upperStar Λ h).obj M ⟶ N),
      (upperStar Λ j).map ((upperStarLowerStarAdjunction Λ h).homEquiv M N t) ≫
          (identityOpenRestriction Λ j i h w).app N =
        (identityOpenPullbackComparison Λ j i h w).inv.app M ≫
          (upperStar Λ i).map t) :
    (∀ (T : Scheme.{u})
      (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ T)) ℤ),
      I.IsKInjective ↔
        CochainComplex.IsKInjective
          (((InternalModuleOperations.equivalence Λ T).functor.mapHomologicalComplex
            (.up ℤ)).obj I)) ∧
    (∀ (I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ D)) ℤ) [I.IsKInjective],
      CochainComplex.IsKInjective
        (((upperStar Λ i).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ (P I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ D)) ℤ) (s : P ⟶ I) [QuasiIso s] [I.IsKInjective],
      (identityOpenDerivedRestriction Λ j i h w).app (DerivedCategory.Q.obj P) ≫
          (upperStar Λ i).mapDerivedCategoryFactors.hom.app P =
        (upperStar Λ j).mapDerivedCategory.map
            ((lowerStar Λ h).rightDerivedFunctor.map (DerivedCategory.Q.map s) ≫
              ((lowerStar Λ h).rightDerivedFunctorObjQIso I).hom) ≫
          (upperStar Λ j).mapDerivedCategoryFactors.hom.app
            (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (identityOpenRestriction Λ j i h w)
              (.up ℤ)).app I) ≫
          inv (DerivedCategory.Q.map (((upperStar Λ i).mapHomologicalComplex
            (.up ℤ)).map s))) ∧
    (∀ P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ D)) ℤ,
      (upperStar Λ j).mapDerivedCategoryFactors.inv.app
          (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (upperStar Λ j).mapDerivedCategory.map
            ((lowerStar Λ h).rightDerivedFunctorUnitQ P) ≫
          (identityOpenDerivedRestriction Λ j i h w).app (DerivedCategory.Q.obj P) ≫
          (upperStar Λ i).mapDerivedCategoryFactors.hom.app P =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (identityOpenRestriction Λ j i h w)
            (.up ℤ)).app P)) ∧
    Functor.IsRightDerivedFunctor
      ((lowerStar Λ h).rightDerivedFunctor ⋙ (upperStar Λ j).mapDerivedCategory)
      (identityOpenLocalizedDerivedUnit Λ j h)
        (HomologicalComplex.quasiIso
          (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
            (condensedRingObj Λ D)) (.up ℤ)) ∧
    (∀ A : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)),
      (upperStar Λ j).mapDerivedCategory.map
          ((identityOpenTermwiseDerivedAdjunction Λ h).unit.app A) ≫
          (identityOpenDerivedRestriction Λ j i h w).app
            ((upperStar Λ h).mapDerivedCategory.obj A) =
        (identityOpenDerivedPullbackComparison Λ j i h w).inv.app A) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ D)),
      (upperStar Λ i).mapDerivedCategory.map
          ((identityOpenTermwiseDerivedAdjunction Λ h).counit.app K) =
        (identityOpenDerivedPullbackComparison Λ j i h w).hom.app
            ((lowerStar Λ h).rightDerivedFunctor.obj K) ≫
          (identityOpenDerivedRestriction Λ j i h w).app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
