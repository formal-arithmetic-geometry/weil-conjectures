/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.ClosedTestScalarModelDiagrams
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Paper.ClosedTestChainModelMapNaturality

/-! # Naturality of closed-test models for actual derived maps

Source: Stacks Tags 070I, 070Y, 0D6F and 09BL
(blueprint: lem-sfb-closed-test-model-map-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
open ClosedTestKInjectiveSectionModels
open ClosedTestDerivedExchangeModel (restrict restrictPush scalarUnit adj pullComp)
variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ]
/-! Resolution-independent naturality of the specified section models.
Source: Stacks Tags 070I, 070Y, 0D6F and 09BL. -/
private theorem representative_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    {K N : DerivedCategory C} (I J : CochainComplex C ℤ) [J.IsKInjective]
    (e : DerivedCategory.Q.obj I ≅ K) (d : DerivedCategory.Q.obj J ≅ N)
    (α : K ⟶ N) (b : I ⟶ J) (hb : DerivedCategory.Q.map b = e.hom ≫ α ≫ d.inv) :
    F.rightDerivedFunctorUnitQ I ≫
        F.rightDerivedFunctor.map (e.hom ≫ α ≫ d.inv) ≫
        (F.rightDerivedFunctorObjQIso J).hom =
      DerivedCategory.Q.map ((complexes F).map b) := by
  rw [← hb, ← F.rightDerivedFunctorUnitQ_naturality_assoc,
    F.rightDerivedFunctorUnitQ_eq]
  simp only [Iso.inv_hom_id, Category.comp_id]

private theorem model_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (H : DerivedCategory C ⥤ DerivedCategory D)
    (σ : complexes F ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ H)
    {K N : DerivedCategory C} (I J : CochainComplex C ℤ) [J.IsKInjective]
    (e : DerivedCategory.Q.obj I ≅ K) (d : DerivedCategory.Q.obj J ≅ N)
    (α : K ⟶ N) :
    (F.rightDerivedFunctorUnitQ I ≫
        F.rightDerivedFunctor.map (e.hom ≫ α ≫ d.inv) ≫
        (F.rightDerivedFunctorObjQIso J).hom) ≫ (σ.app J ≫ H.map d.hom) =
      (σ.app I ≫ H.map e.hom) ≫ H.map α := by
  obtain ⟨b, hb⟩ := CochainComplex.IsKInjective.exists_Q_map_eq I J
    (e.hom ≫ α ≫ d.inv)
  rw [representative_map F I J e d α b hb]
  have hn := σ.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← H.map_comp, hb,
    Iso.inv_hom_id, Category.comp_id]

private noncomputable def computationUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    complexes F ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app I := F.rightDerivedFunctorUnitQ I
  naturality _ _ b := F.rightDerivedFunctorUnitQ_naturality b

@[irreducible] private noncomputable def sourceTransformation
    (A : Type u) [CommRing A] (a : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (V : (Spec (.of (A ⧸ a))).AffineProEt) :
    complexes (evaluation Λ (testFibre f (liftedTest A a V))) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
        (CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategory ⋙
        (evaluation Λ (closedTest A a V)).rightDerivedFunctor) :=
  Functor.whiskerLeft (complexes (CondensedRing.lowerStar Λ f))
    (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (closedUnit Λ A a V) (.up ℤ)) DerivedCategory.Q ≫
      Functor.whiskerLeft (complexes (CondensedRing.upperStar Λ (closedMap A a)))
        (computationUnit (evaluation Λ (closedTest A a V))) ≫
      Functor.whiskerRight
        (CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategoryFactors.inv
        (evaluation Λ (closedTest A a V)).rightDerivedFunctor) ≫
    Functor.whiskerRight (computationUnit (CondensedRing.lowerStar Λ f))
      ((CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategory ⋙
        (evaluation Λ (closedTest A a V)).rightDerivedFunctor)

private theorem sourceModel_eq
    (A : Type u) [CommRing A] (a : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    {K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (e : DerivedCategory.Q.obj I ≅ K) :
    sourceModel Λ A a f V K I e =
      (sourceTransformation (Λ := Λ) A a f V).app I ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
          (CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategory ⋙
          (evaluation Λ (closedTest A a V)).rightDerivedFunctor).map e.hom := by
  simp only [sourceModel, sourceTransformation, computationUnit, closedUnitComplex,
    exactRepresentative, pushModel, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Functor.comp_map, Iso.app_inv,
    Category.assoc]

@[irreducible] private noncomputable def targetTransformation
    {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt) :
    complexes (evaluation Λ (testFibre b W)) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (CondensedRing.moduleObjectDerivedPushforward Λ b ⋙
        (evaluation Λ W).rightDerivedFunctor) :=
  Functor.whiskerLeft (complexes (CondensedRing.lowerStar Λ b))
      (computationUnit (evaluation Λ W)) ≫
    Functor.whiskerRight (computationUnit (CondensedRing.lowerStar Λ b))
      (evaluation Λ W).rightDerivedFunctor

private theorem targetModel_eq_transformation
    {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt)
    {K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (e : DerivedCategory.Q.obj I ≅ K) :
    targetModel Λ b W K I e =
      (targetTransformation (Λ := Λ) b W).app I ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ b ⋙
          (evaluation Λ W).rightDerivedFunctor).map e.hom := by
  simp only [targetModel, pushModel, targetTransformation, computationUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Functor.comp_map, Category.assoc]

@[irreducible] private noncomputable def localizationTransformation {X : Scheme.{u}} (W : X.ProEt) :
    complexes (evaluation Λ W) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ localizedSections Λ W where
  app I := (evaluation Λ W).rightDerivedFunctorUnitQ I ≫
    (derivedLocalization Λ W).app (DerivedCategory.Q.obj I)
  naturality I J a := by
    dsimp only [Functor.comp_map]
    rw [← Category.assoc, Functor.rightDerivedFunctorUnitQ_naturality,
      Category.assoc, (derivedLocalization Λ W).naturality]
    simp only [Functor.comp_map, Category.assoc]

/-- Compare the two supplied models for any actual derived map.
Source: Stacks Tags 070I, 070Y, 0D6F and 09BL
(blueprint: lem-sfb-closed-test-model-map-naturality).
Proof: conjugate the derived arrow by M.e and P.e and represent it by a chain
map into the supplied K-injective target. Computation-unit naturality identifies
modelMap with the image of this chain map. The source and target comparison maps
are components of natural transformations on complexes built from the actual
closed unit, evaluation computation units, exact-pullback factors and pushforward
computation units. Naturality of these transformations and cancellation of the
target representative iso give their two squares. The localization comparison
is another such transformation, giving the two localization squares.

For chain restriction, rightDerivedPullback_app_Q_obj expresses Q of the section
unit followed by j as the source computation unit, source representative, derived
section arrow, inverse target representative, and inverse target computation unit.
Substitute this formula for both models and expand modelMap. Cancel adjacent
representative and computation isomorphisms. The remaining equation is precisely
naturality of derivedSectionArrow at the actual derived arrow. This calculation
uses only K-injectivity of the supplied representatives, so works without
boundedness and depends only on the actual derived map. -/
theorem closed_test_model_map_naturality
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    {K N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (α : K ⟶ N) (M : TestModel Λ h K) (P : TestModel Λ h N) :
    ModelMapCoherence A a f h fZ w V α M P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceModel_eq, sourceModel_eq]
    exact model_naturality (evaluation Λ (testFibre f (liftedTest A a V))) _
      (sourceTransformation (Λ := Λ) A a f V)
      M.I P.I M.e P.e α
  · rw [targetModel_eq_transformation, targetModel_eq_transformation]
    exact model_naturality (evaluation Λ (testFibre fZ (closedTest A a V))) _
      (targetTransformation (Λ := Λ) fZ (closedTest A a V))
      M.J P.J M.pullIso P.pullIso ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α)
  · exact closed_test_chain_model_map_naturality A a f h fZ w V α M P
  · simpa only [localizationTransformation, localizationModel, modelMap, Category.assoc] using
      model_naturality (evaluation Λ (testFibre f (liftedTest A a V))) _
      (localizationTransformation (Λ := Λ) (testFibre f (liftedTest A a V))) M.I P.I M.e P.e α
  · simpa only [localizationTransformation, localizationModel, modelMap, Category.assoc] using
      model_naturality (evaluation Λ (testFibre fZ (closedTest A a V))) _
      (localizationTransformation (Λ := Λ) (testFibre fZ (closedTest A a V)))
      M.J P.J M.pullIso P.pullIso ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α)

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
