module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Sheaf.Paper.ClosedTestUnitEvaluation

import all Sheaf.Paper.ClosedTestUnitEvaluation
import all Sheaf.Paper.WeaklyEtaleDerivedEvaluationRestriction

/-! # Normalized K-injective section models at closed lifted tests

Source: Stacks Project, Tags 0D6F, 08BJ, 09BL, 015F and 04J0
(blueprint: lem-sfb-closed-test-kinjective-section-models).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u uC uD vC vD wC wD

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.upperStarLowerStarAdjunction

namespace AlgebraicGeometry.ProEtale.ClosedTestKInjectiveSectionModels

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Evaluation of the existing internal module's underlying abelian sheaf.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def evaluation {X : Scheme.{u}} (V : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Ab.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙
    sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op V)

/-- Evaluation is additive, using the existing forgetful and section functors.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
instance evaluationAdditive {X : Scheme.{u}} (V : X.ProEt) : (evaluation Λ V).Additive := by
  unfold evaluation
  infer_instance

/-- Termwise application, retaining the original unbounded cochain complex.
Source: Stacks 08BJ (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
abbrev complexes {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] :=
  F.mapHomologicalComplex (.up ℤ)

/-- Literal direct-image section formula, including its differential naturality.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def pushEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEt) :
    CondensedRing.lowerStar Λ f ⋙ evaluation Λ V ≅
      evaluation Λ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V) :=
  Iso.refl _

attribute [local irreducible] CondensedRing.lowerStar

/-- The diagonal test arrow used to evaluate the actual inverse-image unit.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def diagonalTest {X : Scheme.{u}} (V : X.ProEt) :
    Scheme.ProEt.mk (𝟙 V.left) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) rfl)
    (pullback.lift_snd _ _ _)

/-- Restriction of the underlying sections along the actual site arrow.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def evaluationMap {X : Scheme.{u}} {V W : X.ProEt} (a : V ⟶ W) :
    evaluation Λ W ⟶ evaluation Λ V :=
  Functor.whiskerLeft (Mod.forget (condensedRingObj Λ X))
    ((sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).map a.op)

/-- Unit-section map to sections on the localized scheme, without choosing an isomorphism.
Source: Stacks 0D6F, 09BL (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def localizationSections {X : Scheme.{u}} (V : X.ProEt) :
    evaluation Λ V ⟶ CondensedRing.upperStar Λ V.hom ⋙
      evaluation Λ (Scheme.ProEt.mk (𝟙 V.left)) :=
  Functor.whiskerRight (CondensedRing.upperStarLowerStarAdjunction Λ V.hom).unit
      (evaluation Λ V) ≫
    Functor.whiskerLeft (CondensedRing.upperStar Λ V.hom) (pushEvaluation Λ V.hom V).hom ≫
    Functor.whiskerLeft (CondensedRing.upperStar Λ V.hom)
      (evaluationMap Λ (diagonalTest V))

/-- Derived localization map induced by the preceding actual unit-section map.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def derivedLocalization {X : Scheme.{u}} (V : X.ProEt) :
    (evaluation Λ V).rightDerivedFunctor ⟶
      (CondensedRing.upperStar Λ V.hom).mapDerivedCategory ⋙
        (evaluation Λ (Scheme.ProEt.mk (𝟙 V.left))).rightDerivedFunctor :=
  Functor.rightDerivedPullback (CondensedRing.upperStar Λ V.hom)
    (localizationSections Λ V)

/-- The closed immersion in quotient coordinates.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
abbrev closedMap (A : Type u) [CommRing A] (I : Ideal A) :
    Spec (.of (A ⧸ I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The lifted test, regarded in the full small pro-etale site.
Source: Stacks 09BK (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def liftedTest (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj ((Scheme.AffineProEt.closedSiteLift A I).obj V)

/-- The original closed-site test in the full site.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def closedTest (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj V

/-- Base change of a test; its source is the fibre product, with its canonical projection.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def testFibre {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEt) : X.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V

/-- The closed fibre identification, using its actual geometric inclusion.
Source: Stacks 09BK (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def closedFibreArrow (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    closedTest A I V ⟶ testFibre (closedMap A I) (liftedTest A I V) :=
  (ClosedTest.fiberIso A I V).hom

attribute [local semireducible] CondensedRing.lowerStar

/-- The actual module adjunction unit at the lifted test, restricted to its closed fibre.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def closedUnit (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    evaluation Λ (liftedTest A I V) ⟶
      CondensedRing.upperStar Λ (closedMap A I) ⋙ evaluation Λ (closedTest A I V) :=
  Functor.whiskerRight (CondensedRing.upperStarLowerStarAdjunction Λ (closedMap A I)).unit
      (evaluation Λ (liftedTest A I V)) ≫
    Functor.whiskerLeft (CondensedRing.upperStar Λ (closedMap A I))
      ((pushEvaluation Λ (closedMap A I) (liftedTest A I V)).hom ≫
        evaluationMap Λ (closedFibreArrow A I V))

attribute [local irreducible] closedUnit CondensedRing.lowerStar ClosedTest.fiberIso

private lemma closedUnit_app_isIso (A : Type u) [CommRing A] (a : Ideal A)
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)] :
    ∀ F, IsIso ((closedUnit Λ A a V).app F) := by
  let : IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A a).obj V).left, ⊤) :=
    inferInstanceAs (IsWContractibleRing Γ((liftedTest A a V).left, ⊤))
  intro F
  have : IsClosedImmersion (closedMap A a) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) a
  have : IsAffine (liftedTest A a V).left :=
    inferInstanceAs (IsAffine ((Scheme.AffineProEt.closedSiteLift A a).obj V).left)
  have hi : IsIso ((evaluation Λ (liftedTest A a V)).map
      ((CondensedRing.upperStarLowerStarAdjunction Λ (closedMap A a)).unit.app F)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ClosedTest.internalSpecializationUnit_bijective Λ (closedMap A a)
      (liftedTest A a V) (ClosedTest.full_test_surjective _
        ((Scheme.AffineProEt.closedSiteLift A a).obj V))
      (ClosedTest.specializes_pullback (closedMap A a) (liftedTest A a V)
        (Scheme.AffineProEt.closedSiteLiftInclusion A a V) V.hom
        (((Scheme.AffineProEt.affine_closed_site_functor_properties A a).2.2.2.2.2.2.2 V).2.1)
        (((Scheme.AffineProEt.affine_closed_site_functor_properties A a).2.2.2.2.2.2.2 V).2.2)) F
  have : IsIso (closedFibreArrow A a V) := by
    unfold closedFibreArrow
    infer_instance
  have : IsIso (evaluationMap Λ (closedFibreArrow A a V)) := by
    unfold evaluationMap
    infer_instance
  unfold closedUnit
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- The inverse image of a K-injective representative, after its supplied resolution.
Source: Stacks 08BJ (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def pullRepresentative {X Y : Scheme.{u}} (h : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ) (e : DerivedCategory.Q.obj L ≅ K)
    (J : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J) [QuasiIso j] :
    DerivedCategory.Q.obj J ≅ (CondensedRing.upperStar Λ h).mapDerivedCategory.obj K :=
  (asIso (DerivedCategory.Q.map j)).symm ≪≫
    ((CondensedRing.upperStar Λ h).mapDerivedCategoryFactors.app L).symm ≪≫
    (CondensedRing.upperStar Λ h).mapDerivedCategory.mapIso e

/-- The source of derived sections on a localized scheme, with its canonical coefficient.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
abbrev localizedSections {X : Scheme.{u}} (V : X.ProEt) :=
  (CondensedRing.upperStar Λ V.hom).mapDerivedCategory ⋙
    (evaluation Λ (Scheme.ProEt.mk (𝟙 V.left))).rightDerivedFunctor

/-- Canonical section-localization map on a specified representative.
Source: Stacks 0D6F (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def localizationModel {X : Scheme.{u}} (V : X.ProEt)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (e : DerivedCategory.Q.obj L ≅ K) :
    DerivedCategory.Q.obj ((complexes (evaluation Λ V)).obj L) ⟶
      (localizedSections Λ V).obj K :=
  (evaluation Λ V).rightDerivedFunctorUnitQ L ≫
    (derivedLocalization Λ V).app (DerivedCategory.Q.obj L) ≫
    (localizedSections Λ V).map e.hom

private lemma localizationModel_isIso {X : Scheme.{u}} (V : X.ProEt)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) [L.IsKInjective] (e : DerivedCategory.Q.obj L ≅ K) :
    IsIso (localizationModel Λ V K L e) := by
  let : (CondensedRing.upperStar Λ V.hom).PreservesKInjectiveComplexes :=
    CondensedRing.module_weaklyEtale_preservesKInjective Λ V.hom
  have : IsIso (localizationSections Λ V) := by
    have h := CondensedRing.localization_sections_iso Λ V.hom
    have he : localizationSections Λ V =
        CondensedRing.closedFibreModuleSectionsRestriction Λ V.hom
          (Scheme.ProEt.mk V.hom) (𝟙 V.left) (Category.id_comp V.hom) := by
      apply NatTrans.ext
      funext M
      ext x
      rfl
    rw [he]
    exact h
  have : IsIso ((derivedLocalization Λ V).app (DerivedCategory.Q.obj L)) :=
    derived_pullback_iso (CondensedRing.upperStar Λ V.hom) (localizationSections Λ V) _
  unfold localizationModel
  rw [Functor.rightDerivedFunctorUnitQ_eq]
  infer_instance

/-- The actual map between the two test fibres, induced by the closed inclusion.
Source: Stacks 09BK (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def testArrow (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : IsPullback h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    (testFibre fZ (closedTest A I V)).left ⟶ (testFibre f (liftedTest A I V)).left :=
  pullback.map V.hom fZ ((liftedTest A I V).hom) f
    (Scheme.AffineProEt.closedSiteLiftInclusion A I V) h (closedMap A I)
    (((Scheme.AffineProEt.affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V).2.1.w.symm)
    w.w.symm

/-- The coefficient-compatible composition on the actual test square, before deriving.
Source: Stacks 04J0 (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def testPullbackComposition (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : IsPullback h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    CondensedRing.upperStar Λ h ⋙
        CondensedRing.upperStar Λ (testFibre fZ (closedTest A I V)).hom ≅
      CondensedRing.upperStar Λ (testFibre f (liftedTest A I V)).hom ⋙
        CondensedRing.upperStar Λ (testArrow A I w V) :=
  (CondensedRing.upperStarComp Λ (testFibre fZ (closedTest A I V)).hom h).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar Λ) (pullback.lift_snd _ _ _).symm) ≪≫
    CondensedRing.upperStarComp Λ (testArrow A I w V)
      (testFibre f (liftedTest A I V)).hom

/-- The descended coefficient comparison with the canonical termwise localization factors.
Source: Stacks 04J0 (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def derivedTestPullbackComposition (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : IsPullback h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    (CondensedRing.upperStar Λ h).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ (testFibre fZ (closedTest A I V)).hom).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ (testFibre f (liftedTest A I V)).hom).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ (testArrow A I w V)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ h)
      (CondensedRing.upperStar Λ (testFibre fZ (closedTest A I V)).hom)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (testPullbackComposition Λ A I w V) ≪≫
    Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar Λ (testFibre f (liftedTest A I V)).hom)
      (CondensedRing.upperStar Λ (testArrow A I w V))

/-- The canonical resolution comparison in its forward, unit direction.
Source: Stacks 070Y, 08BJ (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def pushModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (e : DerivedCategory.Q.obj L ≅ K) :
    DerivedCategory.Q.obj ((complexes (CondensedRing.lowerStar Λ f)).obj L) ⟶
      (CondensedRing.moduleObjectDerivedPushforward Λ f).obj K :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctorUnitQ L ≫
    (CondensedRing.moduleObjectDerivedPushforward Λ f).map e.hom

/-- Pull an existing resolution map back by an exact functor with its specified factors.
Source: Stacks 015F (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def exactRepresentative {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {L : CochainComplex C ℤ} {K : DerivedCategory C} (r : DerivedCategory.Q.obj L ⟶ K) :
    DerivedCategory.Q.obj ((complexes F).obj L) ⟶ F.mapDerivedCategory.obj K :=
  (F.mapDerivedCategoryFactors.app L).inv ≫ F.mapDerivedCategory.map r

/-- The image of the actual closed-unit section map on the specified complex.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-kinjective-section-models). -/
def closedUnitComplex (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of A)))) ℤ) :
    (complexes (evaluation Λ (liftedTest A I V))).obj L ⟶
      (complexes (evaluation Λ (closedTest A I V))).obj
        ((complexes (CondensedRing.upperStar Λ (closedMap A I))).obj L) :=
  (NatTrans.mapHomologicalComplex (closedUnit Λ A I V) (.up ℤ)).app L

attribute [local semireducible] CondensedRing.lowerStar
attribute [local irreducible] pullRepresentative pushModel exactRepresentative localizationModel

/-- The normalized closed-test models, with the supplied resolutions and actual units.
Source: Stacks Project, Tags 0D6F, 08BJ, 015F, 09BL and 04J0
(blueprint: lem-sfb-closed-test-kinjective-section-models).

Proof:
1. The exact inverse-image adjunctions make both direct images preserve K-injectives.
   The universal derived units on L and J and their given representatives make pushModel
   invertible, including the representative obtained from the quasi-isomorphism j.
2. Exact evaluation at the weakly contractible closed test makes its universal derived
   unit invertible on every complex. Combine it with the exact closed inverse image of
   pushModel to construct eLeft; the corresponding pushModel constructs eRight.
3. The existing closed-test specialization calculation makes the evaluated adjunction
   unit invertible at the lift. The fibre arrow is the existing canonical isomorphism,
   so restriction along it is invertible. Their composite is closedUnit. Apply this
   in each degree and localize to construct eUnit. All three chosen isomorphisms are
   the inverses of the prescribed forward maps, so their inverse equations are reflexive.
4. The existing weakly-etale localization calculation identifies localizationSections
   with the actual diagonal-unit section restriction. Weakly-etale inverse image preserves
   K-injectives, so its derived section restriction is invertible. Compose with the
   evaluation unit on L (respectively J) and the image of the supplied representative.
   This proves both localizationModel assertions without assuming contractible fibres.
5. The coefficient-compatible localized pullback comparison is already the definition
   derivedTestPullbackComposition, using the exact derived compositors and termwise
   descent of the specified testPullbackComposition. No additional comparison is chosen. -/
theorem closed_test_kinjective_section_models
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (L : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [L.IsKInjective] (e : DerivedCategory.Q.obj L ≅ K.obj)
    (J : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1}) (condensedRingObj Λ XZ)) ℤ)
    [J.IsKInjective] (j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J)
    [QuasiIso j] :
    CochainComplex.IsKInjective ((complexes (CondensedRing.lowerStar Λ f)).obj L) ∧
    CochainComplex.IsKInjective ((complexes (CondensedRing.lowerStar Λ fZ)).obj J) ∧
    IsIso (pushModel Λ f K.obj L e) ∧
    IsIso (pushModel Λ fZ ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
      J (pullRepresentative Λ h K.obj L e J j)) ∧
    ∃ eLeft :
        (evaluation Λ (closedTest A a V)).rightDerivedFunctor.obj
            ((CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategory.obj
              ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj)) ≅
          DerivedCategory.Q.obj ((complexes (evaluation Λ (closedTest A a V))).obj
            ((complexes (CondensedRing.upperStar Λ (closedMap A a))).obj
              ((complexes (CondensedRing.lowerStar Λ f)).obj L))),
      ∃ eUnit :
          DerivedCategory.Q.obj ((complexes (evaluation Λ (closedTest A a V))).obj
              ((complexes (CondensedRing.upperStar Λ (closedMap A a))).obj
                ((complexes (CondensedRing.lowerStar Λ f)).obj L))) ≅
            DerivedCategory.Q.obj
              ((complexes (evaluation Λ (testFibre f (liftedTest A a V)))).obj L),
        ∃ eRight :
            (evaluation Λ (closedTest A a V)).rightDerivedFunctor.obj
                ((CondensedRing.moduleObjectDerivedPushforward Λ fZ).obj
                  ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)) ≅
              DerivedCategory.Q.obj ((complexes (evaluation Λ (closedTest A a V))).obj
                ((complexes (CondensedRing.lowerStar Λ fZ)).obj J)),
          eLeft.inv =
            (evaluation Λ (closedTest A a V)).rightDerivedFunctorUnitQ
                ((complexes (CondensedRing.upperStar Λ (closedMap A a))).obj
                  ((complexes (CondensedRing.lowerStar Λ f)).obj L)) ≫
              (evaluation Λ (closedTest A a V)).rightDerivedFunctor.map
                (exactRepresentative (CondensedRing.upperStar Λ (closedMap A a))
                  (pushModel Λ f K.obj L e)) ∧
          eUnit.inv = DerivedCategory.Q.map (closedUnitComplex Λ A a V
            ((complexes (CondensedRing.lowerStar Λ f)).obj L)) ∧
          eRight.inv =
            (evaluation Λ (closedTest A a V)).rightDerivedFunctorUnitQ
                ((complexes (CondensedRing.lowerStar Λ fZ)).obj J) ≫
              (evaluation Λ (closedTest A a V)).rightDerivedFunctor.map
                (pushModel Λ fZ ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
                  J (pullRepresentative Λ h K.obj L e J j)) ∧
          IsIso (localizationModel Λ (testFibre f (liftedTest A a V)) K.obj L e) ∧
          IsIso (localizationModel Λ (testFibre fZ (closedTest A a V))
            ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
            J (pullRepresentative Λ h K.obj L e J j)) := by
  have _square := w
  let : (CondensedRing.lowerStar Λ f).PreservesKInjectiveComplexes :=
    (CondensedRing.upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  let : (CondensedRing.lowerStar Λ fZ).PreservesKInjectiveComplexes :=
    (CondensedRing.upperStarLowerStarAdjunction Λ fZ).preservesKInjectiveComplexes
  have hp : IsIso (pushModel Λ f K.obj L e) := by
    unfold pushModel
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hpZ : IsIso (pushModel Λ fZ
      ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
      J (pullRepresentative Λ h K.obj L e J j)) := by
    unfold pushModel
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  refine ⟨inferInstance, inferInstance, hp, hpZ, ?_⟩
  let : IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A a).obj V).left, ⊤) :=
    inferInstanceAs (IsWContractibleRing Γ((liftedTest A a V).left, ⊤))
  let : (evaluation Λ (closedTest A a V)).PreservesHomology :=
    ClosedTest.internal_test_preservesHomology Λ _ V
  let : PreservesFiniteLimits (evaluation Λ (closedTest A a V)) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits (evaluation Λ (closedTest A a V)) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have hex : IsIso (exactRepresentative (CondensedRing.upperStar Λ (closedMap A a))
      (pushModel Λ f K.obj L e)) := by
    unfold exactRepresentative
    infer_instance
  have heval : ∀ M, IsIso
      ((evaluation Λ (closedTest A a V)).rightDerivedFunctorUnitQ M) := by
    intro M
    unfold Functor.rightDerivedFunctorUnitQ
    infer_instance
  let leftMap :=
    (evaluation Λ (closedTest A a V)).rightDerivedFunctorUnitQ
        ((complexes (CondensedRing.upperStar Λ (closedMap A a))).obj
          ((complexes (CondensedRing.lowerStar Λ f)).obj L)) ≫
      (evaluation Λ (closedTest A a V)).rightDerivedFunctor.map
        (exactRepresentative (CondensedRing.upperStar Λ (closedMap A a))
          (pushModel Λ f K.obj L e))
  let rightMap :=
    (evaluation Λ (closedTest A a V)).rightDerivedFunctorUnitQ
        ((complexes (CondensedRing.lowerStar Λ fZ)).obj J) ≫
      (evaluation Λ (closedTest A a V)).rightDerivedFunctor.map
        (pushModel Λ fZ ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
          J (pullRepresentative Λ h K.obj L e J j))
  have : IsIso leftMap := by
    dsimp only [leftMap]
    have := heval ((complexes (CondensedRing.upperStar Λ (closedMap A a))).obj
      ((complexes (CondensedRing.lowerStar Λ f)).obj L))
    infer_instance
  have : IsIso rightMap := by
    dsimp only [rightMap]
    have := heval ((complexes (CondensedRing.lowerStar Λ fZ)).obj J)
    infer_instance
  have hu := closedUnit_app_isIso Λ A a V
  let : ∀ F, IsIso ((closedUnit Λ A a V).app F) := hu
  have huC : IsIso (closedUnitComplex Λ A a V
      ((complexes (CondensedRing.lowerStar Λ f)).obj L)) := by
    have : ∀ n, IsIso ((closedUnitComplex Λ A a V
        ((complexes (CondensedRing.lowerStar Λ f)).obj L)).f n) := by
      intro n
      change IsIso ((closedUnit Λ A a V).app
        (((complexes (CondensedRing.lowerStar Λ f)).obj L).X n))
      exact hu _
    exact HomologicalComplex.Hom.isIso_of_components _
  let unitMap := DerivedCategory.Q.map (closedUnitComplex Λ A a V
    ((complexes (CondensedRing.lowerStar Λ f)).obj L))
  have : IsIso unitMap := by dsimp only [unitMap]; infer_instance
  refine ⟨(asIso leftMap).symm, (asIso unitMap).symm, (asIso rightMap).symm,
    rfl, rfl, rfl, ?_, ?_⟩
  · exact localizationModel_isIso Λ _ _ _ _
  · exact localizationModel_isIso Λ _ _ _ _

end AlgebraicGeometry.ProEtale.ClosedTestKInjectiveSectionModels
