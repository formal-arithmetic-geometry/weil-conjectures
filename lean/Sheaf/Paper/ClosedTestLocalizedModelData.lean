/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ClosedTestDerivedExchangeModel
public import Sheaf.Paper.ProperWContractibleClosedFibreRigidity
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions


/-!
# Data for resolution and localization coherence of closed-test section models

Source: Stacks Project, derived.tex Tag 070I and sites-cohomology.tex Tags 0D6E and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence

open ClosedTestDerivedExchangeModel

-- Use the canonical structures when comparing the existing section-model interfaces.
attribute [-instance] ClosedTestDerivedExchangeModel.condensedMonoidal
  ClosedTestDerivedExchangeModel.proetaleMonoidal ClosedTestDerivedExchangeModel.moduleAbelian
  ClosedTestDerivedExchangeModel.moduleSectionsAdditive
attribute [instance] ClosedTestDerivedExchangeModel.condensedMonoidal
  ClosedTestDerivedExchangeModel.proetaleMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing evaluation of an internal module, with its scalar action forgotten.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def ev {X : Scheme.{u}} (W : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤ Ab.{u + 1} :=
  CondensedRing.closedFibreModuleEvaluation Λ X W

/-- Evaluation is additive, as is its underlying sheaf evaluation.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
instance ev_additive {X : Scheme.{u}} (W : X.ProEt) : (ev Λ W).Additive :=
  inferInstanceAs (CondensedRing.closedFibreModuleEvaluation Λ X W).Additive

/-- The existing module category over the coefficient pulled back from the point.
Source: module-object convention
(blueprint: def-sfb-closed-test-localized-model-data). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The actual inverse-image unit on sections, followed by a specified site restriction.
Source: Tags 03D3 and 070I
(blueprint: def-sfb-closed-test-localized-model-data). -/
def unitAt {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.ProEt) (W' : X.ProEt)
    (a : W' ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj W) :
    ev Λ W ⟶ CondensedRing.upperStar Λ f ⋙ ev Λ W' :=
  Functor.whiskerRight (CondensedRing.upperStarLowerStarAdjunction Λ f).unit (ev Λ W) ≫
    Functor.whiskerLeft (CondensedRing.upperStar Λ f)
      (Functor.whiskerLeft (Mod.forget (condensedRingObj Λ X))
        ((sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).map a.op))

/-- Ordinary complexes of sections, with their actual differentials.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
abbrev sections {X : Scheme.{u}} (W : X.ProEt) :=
  (ev Λ W).mapHomologicalComplex (.up ℤ)

/-- The universal derived unit as a natural transformation on complexes.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
def derivedUnit {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality _X _Y a := F.rightDerivedFunctorUnitQ_naturality a

/-- The localization comparison as a natural transformation on complexes.
Source: universal derived units, Stacks 070Y and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def localizationTransformation {X : Scheme.{u}} (W : X.ProEt) :
    sections Λ W ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ sectionsOver Λ W.hom :=
  derivedUnit (ev Λ W) ≫ Functor.whiskerLeft DerivedCategory.Q
    (CondensedRing.closedFibreModuleDerivedRestriction Λ W.hom W (𝟙 W.left)
      (Category.id_comp W.hom))

/-- The localized comparison on a complex. The ordinary map is the adjunction unit
restricted to the identity of W; under the slice equivalence it is the degreewise identity.
The remaining factors are the universal derived unit and exact-pullback factorization.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def localizationUnit {X : Scheme.{u}} (W : X.ProEt) (I : CochainComplex (Modules Λ X) ℤ) :
    DerivedCategory.Q.obj ((sections Λ W).obj I) ⟶
      (sectionsOver Λ W.hom).obj (DerivedCategory.Q.obj I) :=
  (localizationTransformation Λ W).app I

variable (A : Type u) [CommRing A] (𝔞 : Ideal A)

/-- The test as an object of the full small pro-etale site.
Source: Tag 09BL (blueprint: def-sfb-closed-test-localized-model-data). -/
def test (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj V

/-- The specified lift as an object of the full small pro-etale site.
Source: Tag 09BL (blueprint: def-sfb-closed-test-localized-model-data). -/
def liftedTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj ((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V)

/-- The geometric map from the closed test into the base change of its specified lift.
Source: Tag 09BK (blueprint: def-sfb-closed-test-localized-model-data). -/
def closedTestArrow (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    test A 𝔞 V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (closedMap A 𝔞)).obj
      (liftedTest A 𝔞 V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (Scheme.AffineProEt.closedSiteLiftInclusion A 𝔞 V) V.hom
      ((Scheme.AffineProEt.affine_closed_site_functor_properties A 𝔞).2.2.2.2.2.2.2 V).2.1.w)
    (pullback.lift_snd _ _ _)

/-- The actual closed unit, evaluated on the specified lift and test.
Source: Tag 09BL (blueprint: def-sfb-closed-test-localized-model-data). -/
def closedUnit (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :=
  unitAt Λ (closedMap A 𝔞) (liftedTest A 𝔞 V) (test A 𝔞 V) (closedTestArrow A 𝔞 V)

variable {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ 𝔞)))
  (w : IsPullback h fZ f (closedMap A 𝔞))

/-- The lifted test fibre as a site object of X.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def sourceTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) : X.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj (liftedTest A 𝔞 V)

/-- The closed test fibre as a site object of X_Z.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def targetTest (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) : XZ.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ fZ).obj (test A 𝔞 V)

/-- The canonical fibre-product map used to evaluate the inverse-image unit.
Source: Tags 09BK and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def fibreTestArrow (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    targetTest A 𝔞 fZ V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj
      (sourceTest A 𝔞 f V) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (pullback.lift
        (pullback.fst V.hom fZ ≫ Scheme.AffineProEt.closedSiteLiftInclusion A 𝔞 V)
        (pullback.snd V.hom fZ ≫ h)
        (by
          change (pullback.fst V.hom fZ ≫
            Scheme.AffineProEt.closedSiteLiftInclusion A 𝔞 V) ≫
              ((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V).hom =
            (pullback.snd V.hom fZ ≫ h) ≫ f
          rw [Category.assoc,
            ((Scheme.AffineProEt.affine_closed_site_functor_properties A 𝔞).2.2.2.2.2.2.2
              V).2.1.w, ← Category.assoc, pullback.condition, Category.assoc, ← w.w]
          simp only [Category.assoc]))
      (pullback.snd V.hom fZ) (pullback.lift_snd _ _ _))
    (pullback.lift_snd _ _ _)

/-- The chain arrow j(T_0) after the actual unit section, localized to D(Ab).
Source: Tag 070I, the arrow r in the statement
(blueprint: def-sfb-closed-test-localized-model-data). -/
def modelArrow (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) (J : CochainComplex (Modules Λ XZ) ℤ)
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    DerivedCategory.Q.obj ((sections Λ (sourceTest A 𝔞 f V)).obj I) ⟶
      DerivedCategory.Q.obj ((sections Λ (targetTest A 𝔞 fZ V)).obj J) :=
  DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex
      (unitAt Λ h (sourceTest A 𝔞 f V) (targetTest A 𝔞 fZ V)
        (fibreTestArrow A 𝔞 f h fZ w V)) (.up ℤ)).app I ≫
      (sections Λ (targetTest A 𝔞 fZ V)).map j)

/-- The complete source comparison, natural on complexes.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
@[irreducible] def sourceTransformation (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    sections Λ (sourceTest A 𝔞 f V) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
        pull Λ (closedMap A 𝔞) ⋙ (ev Λ (test A 𝔞 V)).rightDerivedFunctor :=
  Functor.whiskerLeft ((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ))
    (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (closedUnit Λ A 𝔞 V) (.up ℤ)) DerivedCategory.Q ≫
      Functor.whiskerLeft
        ((CondensedRing.upperStar Λ (closedMap A 𝔞)).mapHomologicalComplex (.up ℤ))
        (derivedUnit (ev Λ (test A 𝔞 V))) ≫
      Functor.whiskerRight
        (CondensedRing.upperStar Λ (closedMap A 𝔞)).mapDerivedCategoryFactors.inv
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor) ≫
    Functor.whiskerRight (derivedUnit (CondensedRing.lowerStar Λ f))
      (pull Λ (closedMap A 𝔞) ⋙ (ev Λ (test A 𝔞 V)).rightDerivedFunctor)

/-- The complete target comparison, natural on complexes.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
@[irreducible] def targetTransformation (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    sections Λ (targetTest A 𝔞 fZ V) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor :=
  Functor.whiskerLeft ((CondensedRing.lowerStar Λ fZ).mapHomologicalComplex (.up ℤ))
      (derivedUnit (ev Λ (test A 𝔞 V))) ≫
    Functor.whiskerRight (derivedUnit (CondensedRing.lowerStar Λ fZ))
      (ev Λ (test A 𝔞 V)).rightDerivedFunctor

/-- The normalized map from the source model to its derived section expression.
Its inverse is exactly the requested source comparison; the closed unit is never replaced
by an unspecified isomorphism.
Source: Tags 070I and 09BL
(blueprint: def-sfb-closed-test-localized-model-data). -/
@[irreducible] def sourceUnit (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj ((sections Λ (sourceTest A 𝔞 f V)).obj I) ⟶
      (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A 𝔞) ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) :=
  (sourceTransformation Λ A 𝔞 f V).app I

/-- The transformation component equals the original sourceUnit composite.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
theorem sourceUnit_eq_original (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective] :
    sourceUnit Λ A 𝔞 f V I =
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (closedUnit Λ A 𝔞 V)
      (.up ℤ)).app (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctorUnitQ
      (((CondensedRing.upperStar Λ (closedMap A 𝔞)).mapHomologicalComplex (.up ℤ)).obj
        (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
      ((CondensedRing.upperStar Λ (closedMap A 𝔞)).mapDerivedCategoryFactors.inv.app
          (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (pull Λ (closedMap A 𝔞)).map
          ((CondensedRing.lowerStar Λ f).rightDerivedFunctorObjQIso I).inv) := by
  simp only [sourceUnit, sourceTransformation, derivedUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.map_comp, Functor.rightDerivedFunctorUnitQ_eq, Category.assoc]

/-- The normalized map from the target section model to its derived expression.
The direct-image section formula is literal; the other factors are resolution units.
Source: Tags 070I and 0D6E
(blueprint: def-sfb-closed-test-localized-model-data). -/
@[irreducible] def targetUnit (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ)
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    DerivedCategory.Q.obj ((sections Λ (targetTest A 𝔞 fZ V)).obj J) ⟶
      (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) :=
  (targetTransformation Λ A 𝔞 fZ V).app J ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
      ((CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
        ((asIso (DerivedCategory.Q.map j)).inv ≫
          (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I))

/-- The transformation component equals the original targetUnit composite.
Source: universal derived units, Stacks 070Y
(blueprint: def-sfb-closed-test-localized-model-data). -/
theorem targetUnit_eq_original (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ)
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    targetUnit Λ A 𝔞 h fZ V I J j =
  (ev Λ (test A 𝔞 V)).rightDerivedFunctorUnitQ
      (((CondensedRing.lowerStar Λ fZ).mapHomologicalComplex (.up ℤ)).obj J) ≫
    (ev Λ (test A 𝔞 V)).rightDerivedFunctor.map
      (((CondensedRing.lowerStar Λ fZ).rightDerivedFunctorObjQIso J).inv ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ fZ).map
          ((asIso (DerivedCategory.Q.map j)).inv ≫
            (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I)) := by
  simp only [targetUnit, targetTransformation, derivedUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Functor.rightDerivedFunctorUnitQ_eq, Category.assoc]

/-- Restriction of underlying sections along a site arrow.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def sectionMap {Y : Scheme.{u}} {W W' : Y.ProEt} (a : W' ⟶ W) : ev Λ W ⟶ ev Λ W' :=
  Functor.whiskerLeft (Mod.forget (condensedRingObj Λ Y))
    ((sheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}).map a.op)

/-- The test map on lifted source fibres, supplied by the actual closed-site functor.
Source: Tag 09BK (blueprint: def-sfb-closed-test-localized-model-data). -/
def sourceTestMap {V V' : (Spec (.of (A ⧸ 𝔞))).AffineProEt} (a : V' ⟶ V) :
    sourceTest A 𝔞 f V' ⟶ sourceTest A 𝔞 f V :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
    ((Scheme.AffineProEt.toProEt _).map ((Scheme.AffineProEt.closedSiteLift A 𝔞).map a))

/-- The test map on target fibres, supplied by scheme base change.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def targetTestMap {V V' : (Spec (.of (A ⧸ 𝔞))).AffineProEt} (a : V' ⟶ V) :
    targetTest A 𝔞 fZ V' ⟶ targetTest A 𝔞 fZ V :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ fZ).map
    ((Scheme.AffineProEt.toProEt _).map a)

/-- A derived morphism represented by comparisons into the two K-injectives.
The equation for v uses Q(j) inverse, so h-star I is not assumed K-injective.
Source: Tag 070I (blueprint: def-sfb-closed-test-localized-model-data). -/
def Represents {I I' : CochainComplex (Modules Λ X) ℤ}
    {J J' : CochainComplex (Modules Λ XZ) ℤ}
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    (j' : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I' ⟶ J')
    [QuasiIso j] [QuasiIso j']
    (α : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I')
    (u : I ⟶ I') (v : J ⟶ J') : Prop :=
  DerivedCategory.Q.map u = α ∧
    DerivedCategory.Q.map v = (asIso (DerivedCategory.Q.map j)).inv ≫
      DerivedCategory.Q.map
        (((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).map u) ≫
      DerivedCategory.Q.map j'

/-- All resolution changes and their normalized comparison squares.
Source: Tag 070I and the universal right-derived units
(blueprint: def-sfb-closed-test-localized-model-data). -/
def ResolutionCoherence (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective]
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] : Prop :=
  ∀ (K' : DerivedCategory.Plus (Modules Λ X))
    (I' : CochainComplex (Modules Λ X) ℤ) [I'.IsKInjective]
    (_e' : DerivedCategory.Q.obj I' ≅ K'.obj)
    (J' : CochainComplex (Modules Λ XZ) ℤ) [J'.IsKInjective]
    (j' : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I' ⟶ J')
    [QuasiIso j'] (α : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I'),
    (∃ (u : I ⟶ I') (v : J ⟶ J'), Represents Λ h j j' α u v) ∧
    (∀ (u : I ⟶ I') (v : J ⟶ J'), Represents Λ h j j' α u v →
      Nonempty (Homotopy (j ≫ v)
        (((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).map u ≫ j')) ∧
      DerivedCategory.Q.map ((sections Λ (sourceTest A 𝔞 f V)).map u) ≫
          modelArrow Λ A 𝔞 f h fZ w V I' J' j' =
        modelArrow Λ A 𝔞 f h fZ w V I J j ≫
          DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map v) ∧
      DerivedCategory.Q.map ((sections Λ (sourceTest A 𝔞 f V)).map u) ≫
          sourceUnit Λ A 𝔞 f V I' =
        sourceUnit Λ A 𝔞 f V I ≫
          (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A 𝔞) ⋙
            (ev Λ (test A 𝔞 V)).rightDerivedFunctor).map α ∧
      DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map v) ≫
          targetUnit Λ A 𝔞 h fZ V I' J' j' =
        targetUnit Λ A 𝔞 h fZ V I J j ≫
          (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
            (ev Λ (test A 𝔞 V)).rightDerivedFunctor).map α ∧
      DerivedCategory.Q.map ((sections Λ (sourceTest A 𝔞 f V)).map u) ≫
          localizationUnit Λ (sourceTest A 𝔞 f V) I' =
        localizationUnit Λ (sourceTest A 𝔞 f V) I ≫
          (sectionsOver Λ (sourceTest A 𝔞 f V).hom).map α ∧
      DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map v) ≫
          localizationUnit Λ (targetTest A 𝔞 fZ V) J' =
        localizationUnit Λ (targetTest A 𝔞 fZ V) J ≫
          (sectionsOver Λ (targetTest A 𝔞 fZ V).hom).map (DerivedCategory.Q.map v) ∧
      (IsIso α →
        IsIso (DerivedCategory.Q.map ((sections Λ (sourceTest A 𝔞 f V)).map u)) ∧
        IsIso (DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map v))) ∧
    (∀ (u u' : I ⟶ I') (v v' : J ⟶ J'),
      Represents Λ h j j' α u v → Represents Λ h j j' α u' v' →
        Nonempty (Homotopy u u') ∧ Nonempty (Homotopy v v')) ∧
    (∀ (u u' : I ⟶ I') (v v' : J ⟶ J'),
      Homotopy u u' → Homotopy v v' →
        DerivedCategory.Q.map ((sections Λ (sourceTest A 𝔞 f V)).map u) =
          DerivedCategory.Q.map ((sections Λ (sourceTest A 𝔞 f V)).map u') ∧
        DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map v) =
          DerivedCategory.Q.map ((sections Λ (targetTest A 𝔞 fZ V)).map v')))

/-- Presheaf test naturality, including both normalized derived comparisons.
Source: Tags 09BL and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def TestCoherence (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective]
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] : Prop :=
  ∀ (V' : (Spec (.of (A ⧸ 𝔞))).AffineProEt) (a : V' ⟶ V),
    IsWContractibleRing Γ(V'.left, ⊤) →
    IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V').left, ⊤) →
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (sectionMap Λ (sourceTestMap A 𝔞 f a)) (.up ℤ)).app I) ≫
        modelArrow Λ A 𝔞 f h fZ w V' I J j =
      modelArrow Λ A 𝔞 f h fZ w V I J j ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (sectionMap Λ (targetTestMap A 𝔞 fZ a)) (.up ℤ)).app J) ∧
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (sectionMap Λ (sourceTestMap A 𝔞 f a)) (.up ℤ)).app I) ≫
        sourceUnit Λ A 𝔞 f V' I =
      sourceUnit Λ A 𝔞 f V I ≫
        (Functor.rightDerivedFunctorNatTrans (sectionMap Λ
          ((Scheme.AffineProEt.toProEt _).map a))).app
          ((CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
            pull Λ (closedMap A 𝔞)).obj (DerivedCategory.Q.obj I)) ∧
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (sectionMap Λ (targetTestMap A 𝔞 fZ a)) (.up ℤ)).app J) ≫
        targetUnit Λ A 𝔞 h fZ V' I J j =
      targetUnit Λ A 𝔞 h fZ V I J j ≫
        (Functor.rightDerivedFunctorNatTrans (sectionMap Λ
          ((Scheme.AffineProEt.toProEt _).map a))).app
          ((pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ).obj
            (DerivedCategory.Q.obj I)) ∧
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (sectionMap Λ (sourceTestMap A 𝔞 f a)) (.up ℤ)).app I) ≫
        localizationUnit Λ (sourceTest A 𝔞 f V') I =
      localizationUnit Λ (sourceTest A 𝔞 f V) I ≫
        (sectionsArrow Λ (sourceTestMap A 𝔞 f a).left
          (MorphismProperty.Over.w (sourceTestMap A 𝔞 f a))).app (DerivedCategory.Q.obj I) ∧
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (sectionMap Λ (targetTestMap A 𝔞 fZ a)) (.up ℤ)).app J) ≫
        localizationUnit Λ (targetTest A 𝔞 fZ V') J =
      localizationUnit Λ (targetTest A 𝔞 fZ V) J ≫
        (sectionsArrow Λ (targetTestMap A 𝔞 fZ a).left
          (MorphismProperty.Over.w (targetTestMap A 𝔞 fZ a))).app (DerivedCategory.Q.obj J)

/-- The closed map between the actual section-test fibres. The order of fibre-product
factors follows the existing site API; the projections identify these with T and T_0.
Source: Tags 09BK and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def closedFibreMap (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    (targetTest A 𝔞 fZ V).left ⟶ (sourceTest A 𝔞 f V).left :=
  (fibreTestArrow A 𝔞 f h fZ w V).left ≫
    pullback.fst (sourceTest A 𝔞 f V).hom h

/-- Localized restriction between the actual test fibres, with coefficient composition.
Source: Tags 09T5 and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def localizedRestriction (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) :
    sectionsOver Λ (sourceTest A 𝔞 f V).hom ⟶
      pull Λ h ⋙ sectionsOver Λ (targetTest A 𝔞 fZ V).hom :=
  sectionsArrow Λ (closedFibreMap A 𝔞 f h fZ w V)
    (by
      dsimp only [closedFibreMap]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun q ↦ q ≫ h) (MorphismProperty.Over.w
        (fibreTestArrow A 𝔞 f h fZ w V))) ≫
    Functor.whiskerRight (pullComp Λ (targetTest A 𝔞 fZ V).hom h).hom
      (condensedModuleSections Λ (targetTest A 𝔞 fZ V).left).rightDerivedFunctor

/-- The normalized model arrow is the actual localized derived restriction.
Source: Tags 070I and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def LocalizedModelEquation (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ)
    (J : CochainComplex (Modules Λ XZ) ℤ)
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] : Prop :=
  modelArrow Λ A 𝔞 f h fZ w V I J j ≫
      localizationUnit Λ (targetTest A 𝔞 fZ V) J ≫
      (sectionsOver Λ (targetTest A 𝔞 fZ V).hom).map
        ((asIso (DerivedCategory.Q.map j)).inv ≫
          (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I) =
    localizationUnit Λ (sourceTest A 𝔞 f V) I ≫
      (localizedRestriction Λ A 𝔞 f h fZ w V).app (DerivedCategory.Q.obj I)

/-- Evaluation versus sections on the localized site, with the actual unit normalization.
Source: Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
def evaluationLocalization {Y : Scheme.{u}} (W : Y.ProEt) :=
  CondensedRing.closedFibreModuleDerivedRestriction Λ W.hom W (𝟙 W.left)
    (Category.id_comp W.hom)

/-- The reused localization construction is normalized by the original section unit.
Source: Stacks Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
theorem evaluationLocalization_eq_original {Y : Scheme.{u}} (W : Y.ProEt) :
    evaluationLocalization Λ W =
      CondensedRing.closedFibreModuleDerivedRestriction Λ W.hom W (𝟙 W.left)
        (Category.id_comp W.hom) := by
  rfl

/-- Reusing the model construction preserves the original termwise localization formula.
Source: Stacks Tag 0D6G (blueprint: def-sfb-closed-test-localized-model-data). -/
theorem localizationUnit_eq_original {Y : Scheme.{u}} (W : Y.ProEt)
    (I : CochainComplex (Modules Λ Y) ℤ) :
    localizationUnit Λ W I =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (CondensedRing.closedFibreModuleSectionsRestriction Λ W.hom W (𝟙 W.left)
          (Category.id_comp W.hom)) (.up ℤ)).app I) ≫
        (condensedModuleSections Λ W.left).rightDerivedFunctorUnitQ
          (((CondensedRing.upperStar Λ W.hom).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (condensedModuleSections Λ W.left).rightDerivedFunctor.map
          ((CondensedRing.upperStar Λ W.hom).mapDerivedCategoryFactors.inv.app I) := by
  change (ev Λ W).rightDerivedFunctorUnitQ I ≫
      (evaluationLocalization Λ W).app (DerivedCategory.Q.obj I) = _
  rw [evaluationLocalization_eq_original]
  exact Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app'
    (CondensedRing.upperStar Λ W.hom)
    (CondensedRing.closedFibreModuleSectionsRestriction Λ W.hom W (𝟙 W.left)
      (Category.id_comp W.hom)) I

/-- The four comparison isomorphisms, pinned to the actual model units and section formulas.
The first displayed equation uses the inverse closed unit; the second is direct-image
section evaluation. These equations connect geometric comparison squares to the models.
Source: Tags 09BL, 070I and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def NormalizedComparisons (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt)
    (I : CochainComplex (Modules Λ X) ℤ) [I.IsKInjective]
    (J : CochainComplex (Modules Λ XZ) ℤ) [J.IsKInjective]
    (j : ((CondensedRing.upperStar Λ h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] : Prop :=
  ∃ (eC : (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A 𝔞) ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) ≅
        DerivedCategory.Q.obj ((sections Λ (sourceTest A 𝔞 f V)).obj I))
    (eD : (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
        (ev Λ (test A 𝔞 V)).rightDerivedFunctor).obj (DerivedCategory.Q.obj I) ≅
        DerivedCategory.Q.obj ((sections Λ (targetTest A 𝔞 fZ V)).obj J))
    (eV : (ev Λ (test A 𝔞 V)).rightDerivedFunctor ≅ sectionsOver Λ V.hom),
    eC.inv = sourceUnit Λ A 𝔞 f V I ∧
    eD.inv = targetUnit Λ A 𝔞 h fZ V I J j ∧
    eV.hom = evaluationLocalization Λ (test A 𝔞 V) ∧
    (closedComparison Λ A 𝔞 V).app
        ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj (DerivedCategory.Q.obj I)) ≫
      eV.inv.app ((CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
        pull Λ (closedMap A 𝔞)).obj (DerivedCategory.Q.obj I)) ≫
      eC.hom ≫ localizationUnit Λ (sourceTest A 𝔞 f V) I =
        (sectionComparison Λ (IsPullback.of_hasPullback
          ((Scheme.AffineProEt.closedSiteLift A 𝔞).obj V).hom f).flip.toCommSq).app
          (DerivedCategory.Q.obj I) ∧
    eV.inv.app ((pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ).obj
        (DerivedCategory.Q.obj I)) ≫
      eD.hom ≫ localizationUnit Λ (targetTest A 𝔞 fZ V) J ≫
      (sectionsOver Λ (targetTest A 𝔞 fZ V).hom).map
        ((asIso (DerivedCategory.Q.map j)).inv ≫
          (CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.inv.app I) =
        (sectionComparison Λ (IsPullback.of_hasPullback V.hom fZ).flip.toCommSq).app
          ((pull Λ h).obj (DerivedCategory.Q.obj I))

/-- Ordinary pullback composition on a square, before deriving.
Source: Tag 04IF (blueprint: def-sfb-closed-test-localized-model-data). -/
def ordinarySquare {Y S Y' S' : Scheme.{u}}
    {b : Y ⟶ S} {b' : Y' ⟶ S'} {q : S' ⟶ S} {p : Y' ⟶ Y}
    (sq : IsPullback p b' b q) :
    CondensedRing.upperStar Λ q ⋙ CondensedRing.upperStar Λ b' ≅
      CondensedRing.upperStar Λ b ⋙ CondensedRing.upperStar Λ p :=
  (CondensedRing.upperStarComp Λ b' q).symm ≪≫
    eqToIso (congrArg (fun z : Y' ⟶ S ↦ CondensedRing.upperStar Λ z) sq.w.symm) ≪≫
    CondensedRing.upperStarComp Λ p b

/-- Ordinary localized direct-image comparison. For a localization its underlying map is
(f-star F)(W) = F(Y times_S W), the degreewise identity of the statement.
Source: Tag 04IF (blueprint: def-sfb-closed-test-localized-model-data). -/
def ordinaryExchange {Y S Y' S' : Scheme.{u}}
    {b : Y ⟶ S} {b' : Y' ⟶ S'} {q : S' ⟶ S} {p : Y' ⟶ Y}
    (sq : IsPullback p b' b q) :
    CondensedRing.lowerStar Λ b ⋙ CondensedRing.upperStar Λ q ⟶
      CondensedRing.upperStar Λ p ⋙ CondensedRing.lowerStar Λ b' :=
  Adjunction.squareExchange (CondensedRing.upperStarLowerStarAdjunction Λ b)
    (CondensedRing.upperStarLowerStarAdjunction Λ b')
    (CondensedRing.upperStar Λ q) (CondensedRing.upperStar Λ p) (ordinarySquare Λ sq)

/-- Localization preserves the actual units and counits. These equations specify the mate
of pullback composition; its component is invertible only for the pro-etale base change.
Source: Tags 04IF and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def LocalizationAdjunction {Y S Y' S' : Scheme.{u}}
    {b : Y ⟶ S} {b' : Y' ⟶ S'} {q : S' ⟶ S} {p : Y' ⟶ Y}
    (sq : IsPullback p b' b q) : Prop :=
  (∀ (I : CochainComplex (Modules Λ Y) ℤ) [I.IsKInjective],
    CochainComplex.IsKInjective
      (((CondensedRing.upperStar Λ p).mapHomologicalComplex (.up ℤ)).obj I)) ∧
  (∀ (I : CochainComplex (Modules Λ Y) ℤ) [I.IsKInjective],
    (pull Λ q).map ((CondensedRing.lowerStar Λ b).rightDerivedFunctorUnitQ I) ≫
        (exchange Λ sq.toCommSq).app (DerivedCategory.Q.obj I) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ b').map
          ((CondensedRing.upperStar Λ p).mapDerivedCategoryFactors.hom.app I) =
      (CondensedRing.upperStar Λ q).mapDerivedCategoryFactors.hom.app
          (((CondensedRing.lowerStar Λ b).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (ordinaryExchange Λ sq) (.up ℤ)).app I) ≫
        (CondensedRing.lowerStar Λ b').rightDerivedFunctorUnitQ
          (((CondensedRing.upperStar Λ p).mapHomologicalComplex (.up ℤ)).obj I)) ∧
  (∀ M : DerivedCategory (Modules Λ Y), IsIso ((exchange Λ sq.toCommSq).app M)) ∧
  (∀ N : DerivedCategory (Modules Λ S),
    (pull Λ q).map ((adj Λ b).unit.app N) ≫
        (exchange Λ sq.toCommSq).app ((pull Λ b).obj N) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ b').map
          ((square Λ sq.toCommSq).inv.app N) =
      (adj Λ b').unit.app ((pull Λ q).obj N)) ∧
  (∀ M : DerivedCategory (Modules Λ Y),
    (square Λ sq.toCommSq).hom.app
        ((CondensedRing.moduleObjectDerivedPushforward Λ b).obj M) ≫
        (pull Λ p).map ((adj Λ b).counit.app M) =
      (pull Λ b').map ((exchange Λ sq.toCommSq).app M) ≫
        (adj Λ b').counit.app ((pull Λ p).obj M))

/-- The geometric localization squares, on canonical derived section comparisons.
The cube contains all fibre-product projections; isomorphisms of squares are included.
Each admissible local test uses its own closed lift and its own model comparisons.
Source: Tags 04IF, 0D6E and 0D6G
(blueprint: def-sfb-closed-test-localized-model-data). -/
def GeometricCoherence (V : (Spec (.of (A ⧸ 𝔞))).AffineProEt) : Prop :=
  (∀ {Y S Y' S' : Scheme.{u}} {b : Y ⟶ S} {b' : Y' ⟶ S'}
      {q : S' ⟶ S} {p : Y' ⟶ Y},
      (HEq b f ∨ HEq b h ∨ HEq b fZ ∨ HEq b (closedMap A 𝔞)) → WeaklyEtale q →
      ∀ sq : IsPullback p b' b q, LocalizationAdjunction Λ sq) ∧
  (∀ {T W T' W' : Scheme.{u}} (a : W ⟶ T) (a' : W' ⟶ T')
      (t : T' ⟶ T) (k : W' ⟶ W),
      HEq a (closedFibreMap A 𝔞 f h fZ w V) → WeaklyEtale t →
      ∀ (sq : IsPullback k a' a t) (K : DerivedCategory.Plus (Modules Λ T)),
    (restriction Λ a).app K.obj ≫
        (restriction Λ k).app ((pull Λ a).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ k a).inv.app K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((eqToIso (congrArg (fun q : W' ⟶ T ↦ pull Λ q) sq.w)).hom.app K.obj) =
      (restriction Λ t).app K.obj ≫
        (restriction Λ a').app ((pull Λ t).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ a' t).inv.app K.obj)) ∧
  (∀ {Y S T W Y' S' T' W' : Scheme.{u}}
      {b : Y ⟶ S} {c : W ⟶ S} {a : T ⟶ Y} {bW : T ⟶ W}
      {b' : Y' ⟶ S'} {c' : W' ⟶ S'} {a' : T' ⟶ Y'} {bW' : T' ⟶ W'}
      (p : Y' ⟶ Y) (q : S' ⟶ S) (t : T' ⟶ T) (k : W' ⟶ W),
      (HEq b f ∨ HEq b fZ) → WeaklyEtale q → WeaklyEtale c → WeaklyEtale c' →
      ∀ (sq : IsPullback a bW b c) (sq' : IsPullback a' bW' b' c')
      (sb : IsPullback p b' b q) (sc : IsPullback k c' c q)
      (sa : IsPullback t a' a p), IsPullback t bW' bW k →
      ∀ K : DerivedCategory.Plus (Modules Λ Y),
    (sectionComparison Λ sq.toCommSq).app K.obj ≫
        (sectionsArrow Λ t sa.w).app K.obj ≫
        (condensedModuleSections Λ T').rightDerivedFunctor.map
          ((pullComp Λ a' p).hom.app K.obj) =
      (sectionsArrow Λ k sc.w).app
          ((CondensedRing.moduleObjectDerivedPushforward Λ b).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ c' q).hom.app
            ((CondensedRing.moduleObjectDerivedPushforward Λ b).obj K.obj)) ≫
        (sectionsOver Λ c').map ((exchange Λ sb.toCommSq).app K.obj) ≫
        (sectionComparison Λ sq'.toCommSq).app ((pull Λ p).obj K.obj))

end AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence
