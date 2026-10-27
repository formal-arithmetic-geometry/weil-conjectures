/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.SectionDerivedPushpullNormalization
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.SectionRingLaxPushforwardCoherence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation

/-! # Normalized module and section-module direct-image comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0D6E; derived.tex, Tags 08BJ and 070Y
(blueprint: lem-sfb-module-section-derived-comparison-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.all false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

/-- Derive the inverse ordinary internal compositor using the canonical resolution units.
Source: Stacks 070Y and 08BJ
(blueprint: lem-sfb-module-section-derived-comparison-square). -/
def internalPushComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    internalDerivedPushforward Λ (f ≫ g) ≅
      internalDerivedPushforward Λ f ⋙ internalDerivedPushforward Λ g :=
  letI := (CondensedRing.upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorNatIso (CondensedRing.lowerStarComp Λ f g).symm ≪≫
    Functor.rightDerivedFunctorCompIso (CondensedRing.lowerStar Λ f) (CondensedRing.lowerStar Λ g)

/-- Derive the geometric sectionwise compositor, independently of internal realization.
The exact ringed inverse image makes its right adjoint preserve K-injectives.
Source: Stacks 0D6E, with its K-injective normalization
(blueprint: lem-sfb-module-section-derived-comparison-square). -/
def sectionPushComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPushforward Λ (f ≫ g) ≅ derivedPushforward Λ f ⋙ derivedPushforward Λ g :=
  letI := (adjunction Λ f).preservesKInjectiveComplexes
  letI := pushforward_additive Λ f
  letI := pushforward_additive Λ g
  letI : (pushforward Λ f ⋙ pushforward Λ g).Additive := inferInstance
  Functor.rightDerivedFunctorNatIso (pushforwardComposition Λ f g).symm ≪≫
    Functor.rightDerivedFunctorCompIso (pushforward Λ f) (pushforward Λ g)

/-- The internal identity comparison is the derivation of the ordinary identity map.
Source: Stacks 070Y (blueprint: lem-sfb-module-section-derived-comparison-square). -/
def internalPushIdentity (T : Scheme.{u}) :
    internalDerivedPushforward Λ (𝟙 T) ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (CondensedRing.lowerStarId Λ T) ≪≫
    (𝟭 (internalModules Λ T)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryIdIso (internalModules Λ T)

/-- The ordinary sectionwise identity comparison, transported through the fixed equivalence.
Its geometric section formula is asserted below, so its normalization is explicit.
Source: Stacks 03D6 (blueprint: lem-sfb-module-section-derived-comparison-square). -/
def sectionPushIdentity (T : Scheme.{u}) : pushforward Λ (𝟙 T) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (equivalence Λ T).counitIso.symm (pushforward Λ (𝟙 T)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (equivalence Λ T).inverse (pushComparison Λ (𝟙 T)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (equivalence Λ T).inverse (CondensedRing.lowerStarId Λ T))
      (equivalence Λ T).functor ≪≫
    Functor.isoWhiskerRight (Functor.rightUnitor (equivalence Λ T).inverse)
      (equivalence Λ T).functor ≪≫
    (equivalence Λ T).counitIso

/-- The sectionwise derived identity is induced by the ordinary geometric identity.
Source: Stacks 070Y (blueprint: lem-sfb-module-section-derived-comparison-square). -/
def derivedSectionPushIdentity (T : Scheme.{u}) :
    derivedPushforward Λ (𝟙 T) ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (sectionPushIdentity Λ T) ≪≫
    (𝟭 (modules Λ T)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryIdIso (modules Λ T)

/-- The existing internal resolution unit, with its cochain source and target named once.
Source: Stacks 070Y (blueprint: lem-sfb-module-section-derived-comparison-square). -/
def internalPushResolutionUnit {S T : Scheme.{u}} (h : S ⟶ T)
    (P : CochainComplex (internalModules Λ S) ℤ) :
    DerivedCategory.Q.obj
        (((CondensedRing.lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (internalDerivedPushforward Λ h).obj (DerivedCategory.Q.obj P) :=
  (CondensedRing.lowerStar Λ h).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- The existing sectionwise resolution unit, with its actual cochain source and target.
Source: Stacks 070Y (blueprint: lem-sfb-module-section-derived-comparison-square). -/
def sectionPushResolutionUnit {S T : Scheme.{u}} (h : S ⟶ T)
    (P : CochainComplex (modules Λ S) ℤ) :
    DerivedCategory.Q.obj (((pushforward Λ h).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (derivedPushforward Λ h).obj (DerivedCategory.Q.obj P) :=
  (pushforward Λ h).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- Composition and identity squares with their coefficient and resolution normalizations.
Source: Stacks 0D6E, specialized to pulled-back condensed coefficients; Tags 03D6,
08BJ and 070Y (blueprint: lem-sfb-module-section-derived-comparison-square).

Proof plan (the eight steps of the DAG node):
1. Reconstruct eta_f using coefficientMap_existsUnique. Apply
   lem-sfb-section-ring-lax-pushforward-coherence with the geometric pullbackComp;
   def-sfb-finite-lower-star-comp and lem-sfb-eta-comp identify its coefficient map.
2. The same coherence theorem identifies the ordinary module square. Its uniqueness
   and the identity-on-sections normalization in def-pd-section-module-operations-data
   identify r_f; lem-sfb-eta-id gives the identity square.
3. Use lem-pd-section-derived-pushpull-normalization to localize E and identify
   K-injectivity, resolutions and the comparison a_f with its resolution unit square.
4. Exactness of pullback (det-prop-sfb-module-pullback-exact-main) and the specified
   adjunction give preservation of K-injectives by each internal pushforward,
   by lem-weil-pbc-right-adjoint-preserves-kinjective; transport gives the section case.
5. The universal property of def-sfb-right-derived-functor gives the equation with
   gamma_g, gamma_f and Q(c inverse). On K-injectives the resolution units are
   invertible, giving exactly the class of c inverse; similarly for the identity d.
   lem-sf-kinjective-derived-map-computation makes these coordinates canonical.
6. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition independently
   on sections. Taking the intermediate resolution to be the identity gives
   Q(c_s inverse), and termwise identity gives Q(d_s).
7. On a K-injective I, a_g is represented by r_g at f_*I and Rg_s(a_f) by
   g_s(r_f). Inverting the ordinary compositor square of step 2 identifies the
   two composites. The identity square is the same calculation with d.
8. For an arbitrary derived object choose a K-injective representative using
   prop-pur-kinjective-resolutions-exist. Naturality extends both equalities;
   the canonical resolution transitions of lem-sf-kinjective-derived-map-computation
   ensure independence of the representative. All compositions retain the geometric
   associators and the equality transports of the actual scheme maps. -/
theorem moduleSectionDerivedComparisonSquare {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (∀ V : Z.ProEtᵒᵖ,
      (coefficientMap Λ (f ≫ g)).hom.app V =
        (coefficientMap Λ g).hom.app V ≫
          (coefficientMap Λ f).hom.app ((InternalModuleOperations.siteMap g).op.obj V) ≫
          (InternalModuleOperations.ring Λ X).obj.map
            ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
              f g (f ≫ g) rfl).hom.app V.unop).op) ∧
    (∀ M : internalModules Λ X,
      (equivalence Λ Z).functor.map ((CondensedRing.lowerStarComp Λ f g).hom.app M) ≫
          (pushComparison Λ (f ≫ g)).hom.app M =
        (pushComparison Λ g).hom.app ((CondensedRing.lowerStar Λ f).obj M) ≫
          (pushforward Λ g).map ((pushComparison Λ f).hom.app M) ≫
          (pushforwardComposition Λ f g).hom.app ((equivalence Λ X).functor.obj M)) ∧
    (∀ (T : Scheme.{u}) (M : modules Λ T),
      (SheafOfModules.toSheaf _).map ((sectionPushIdentity Λ T).hom.app M) =
        (ProEtale.lowerStarId Ab.{u + 1} T).hom.app
          ((SheafOfModules.toSheaf _).obj M)) ∧
    (∀ (T : Scheme.{u}) (M : internalModules Λ T),
      (equivalence Λ T).functor.map ((CondensedRing.lowerStarId Λ T).hom.app M) =
        (pushComparison Λ (𝟙 T)).hom.app M ≫
          (sectionPushIdentity Λ T).hom.app ((equivalence Λ T).functor.obj M)) ∧
    (∀ T : Scheme.{u}, (derivedFunctor Λ T).IsEquivalence) ∧
    (∀ (T : Scheme.{u}) (I : CochainComplex (internalModules Λ T) ℤ),
      CochainComplex.IsKInjective
        (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj I) ↔ I.IsKInjective) ∧
    (∀ (T : Scheme.{u}) (P I : CochainComplex (internalModules Λ T) ℤ) (i : P ⟶ I),
      (QuasiIso (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).map i) ∧
        CochainComplex.IsKInjective
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj I)) ↔
        (QuasiIso i ∧ I.IsKInjective)) ∧
    (∀ {S T : Scheme.{u}} (h : S ⟶ T),
      (CondensedRing.lowerStar Λ h).PreservesKInjectiveComplexes) ∧
    (∀ {S T : Scheme.{u}} (h : S ⟶ T)
      (P : CochainComplex (internalModules Λ S) ℤ),
      (derivedEquivalence Λ T).functor.map
          (internalPushResolutionUnit Λ h P) ≫
          (derivedPushComparison Λ h).hom.app (DerivedCategory.Q.obj P) ≫
          (derivedPushforward Λ h).map (sectionLocalizationComparison Λ S P).hom =
        (sectionLocalizationComparison Λ T
          (((CondensedRing.lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (pushComparison Λ h) (.up ℤ)).hom.app P) ≫
          sectionPushResolutionUnit Λ h
            (((equivalence Λ S).functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ (M : DerivedCategory (internalModules Λ X)),
      (derivedEquivalence Λ Z).functor.map ((internalPushComposition Λ f g).hom.app M) ≫
          (derivedPushComparison Λ g).hom.app ((internalDerivedPushforward Λ f).obj M) ≫
          (derivedPushforward Λ g).map ((derivedPushComparison Λ f).hom.app M) =
        (derivedPushComparison Λ (f ≫ g)).hom.app M ≫
          (sectionPushComposition Λ f g).hom.app ((derivedEquivalence Λ X).functor.obj M)) ∧
    (∀ (T : Scheme.{u}) (M : DerivedCategory (internalModules Λ T)),
      (derivedEquivalence Λ T).functor.map ((internalPushIdentity Λ T).hom.app M) =
        (derivedPushComparison Λ (𝟙 T)).hom.app M ≫
          (derivedSectionPushIdentity Λ T).hom.app ((derivedEquivalence Λ T).functor.obj M)) ∧
    (∀ (I : CochainComplex (internalModules Λ X) ℤ) [I.IsKInjective],
      internalPushResolutionUnit Λ (f ≫ g) I ≫
          (internalPushComposition Λ f g).hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (CondensedRing.lowerStarComp Λ f g).symm
              (.up ℤ)).hom.app I) ≫
          internalPushResolutionUnit Λ g
            (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
          (internalDerivedPushforward Λ g).map
            (internalPushResolutionUnit Λ f I)) ∧
    (∀ (I : CochainComplex (modules Λ X) ℤ) [I.IsKInjective]
      (J : CochainComplex (modules Λ Y) ℤ) [J.IsKInjective]
      (j : ((pushforward Λ f).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
      QuasiIso (((pushforward Λ g).mapHomologicalComplex (.up ℤ)).map j) ∧
      sectionPushResolutionUnit Λ (f ≫ g) I ≫
          (sectionPushComposition Λ f g).hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (pushforwardComposition Λ f g).symm
              (.up ℤ)).hom.app I) ≫
          DerivedCategory.Q.map (((pushforward Λ g).mapHomologicalComplex (.up ℤ)).map j) ≫
          sectionPushResolutionUnit Λ g J ≫
          (derivedPushforward Λ g).map (inv (DerivedCategory.Q.map j) ≫
            sectionPushResolutionUnit Λ f I)) ∧
    (∀ (T : Scheme.{u}) (I : CochainComplex (internalModules Λ T) ℤ) [I.IsKInjective],
      internalPushResolutionUnit Λ (𝟙 T) I ≫
          (internalPushIdentity Λ T).hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (CondensedRing.lowerStarId Λ T) (.up ℤ)).hom.app I)) := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
