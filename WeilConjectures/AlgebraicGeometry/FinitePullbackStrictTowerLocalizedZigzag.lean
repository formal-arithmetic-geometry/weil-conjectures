/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FinitePullbackStrictTowerLocalizedZigzagData

/-! # Naturality of the localized strict-tower zigzag

Source: Stacks Project, Tags 099N(5), 0G7E, 06XN, 03EL and 0FNH.
(blueprint: lem-a1-finite-pullback-localized-zigzag).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FinitePullbackStrictTower
attribute [local implicit_reducible] asIso
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
attribute [local implicit_reducible] H tensorReduction augmentation G diagramPull
  finiteComplex pulledReduction transpose PrincipalQuotientCompletion.transpose
  koszulTowerComplex HomologicalComplex.asFunctor
  PrincipalKoszulStrictReplacement.sourceTower PrincipalKoszulStrictReplacement.targetTower
  FinitePullbackStrictTowerData.G FinitePullbackStrictTowerData.koszuls
  FinitePullbackStrictTowerData.reductions FinitePullbackStrictTowerData.diagramPull
  FinitePullbackStrictTowerData.finite FinitePullbackStrictTowerData.augmentation
  FinitePullbackStrictTowerData.H FinitePullbackStrictTowerData.tensorReduction
  FinitePullbackStrictTowerData.finiteComplex
  CompletedTowerIndependent.towerPull koszulTowerComplexMap
  PrincipalKoszulStrictReplacement.tensorWith
  PrincipalKoszulStrictReplacement.sourceTowerMap PrincipalKoszulStrictReplacement.targetTowerMap
  CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.map₂HomologicalComplex
  SheafOfModules.KFlatTotalTensorModel.tensor
attribute [local irreducible] CompletedTowerIndependent.reductionPair
  CompletedTowerIndependent.derivedPull CompletedTowerIndependent.derivedCounit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

private def comparisonAug (W : Scheme.{t}) :
    FinitePullbackStrictTowerData.koszuls l E W ⟶
      FinitePullbackStrictTowerData.reductions l E W :=
  { app := augmentation l E W
    naturality := fun _ _ f ↦
      PrincipalKoszulStrictReplacement.comparison_naturality l E W f }

private def comparisonZ
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    (P : CochainComplex (Modules l E Y) ℤ) :
    (((towerPull l E g).mapHomologicalComplex (.up ℤ)).obj
      ((transpose l E Y).obj (PrincipalKoszulStrictReplacement.sourceTower l E Y P))) ⟶
    ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).obj P) :=
  (comparisonKoszulChainIso l E g θ P).hom ≫
    (transpose l E X).map (augmentation l E X ((G l E g).obj P)) ≫
    (comparisonBalancedChainIso l E g lambda P).hom

attribute [local implicit_reducible] comparisonAug comparisonZQ
attribute [local irreducible] comparisonKoszulIso comparisonBalancedIso

private theorem comparisonZ_naturality
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P') :
    (((towerPull l E g).mapHomologicalComplex (.up ℤ)).map
      ((transpose l E Y).map (PrincipalKoszulStrictReplacement.sourceTowerMap l E Y f))) ≫
        comparisonZ l E g θ lambda P' =
      comparisonZ l E g θ lambda P ≫
        ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f) := by
  have h := (θ.hom ≫ Functor.whiskerLeft (G l E g) (comparisonAug l E X) ≫
    lambda.hom).naturality f
  apply HomologicalComplex.hom_ext
  intro i
  apply NatTrans.ext
  funext n
  simpa only [comparisonZ, comparisonKoszulChainIso, comparisonBalancedChainIso,
    comparisonKoszulDiagramIso, comparisonBalancedDiagramIso,
    Functor.mapIso, HomologicalComplex.comp_f, NatTrans.comp_app, comparisonAug,
    transpose, PrincipalQuotientCompletion.transpose, koszulTowerComplexMap,
    Functor.mapHomologicalComplex, CompletedTowerIndependent.towerPull,
    FinitePullbackStrictTowerData.diagramPull, FinitePullbackStrictTowerData.G,
    FinitePullbackStrictTowerData.koszuls, PrincipalKoszulStrictReplacement.sourceTowerMap,
    FinitePullbackStrictTowerData.finite, FinitePullbackStrictTowerData.finiteComplex,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex, HomologicalComplex.asFunctor,
    Functor.comp_map, Functor.whiskeringLeft, Functor.whiskeringRight,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.app_hom] using
      HomologicalComplex.congr_hom (NatTrans.congr_app h n) i

/-- The localized Koszul-augmentation-balanced zigzag is natural in chain maps.
Source: Stacks 0G7E and 06XN. Whisker the natural Koszul, augmentation and balanced
transformations by transposition and localization. Transposition commutes degreewise
with pullback and is inverse, on morphisms, to the complex-of-functors construction.
Their composite naturality equation is the required equation.
(blueprint: lem-a1-finite-pullback-localized-zigzag). -/
theorem comparisonZQ_naturality
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P') : DerivedCategory.Q.map
      (((towerPull l E g).mapHomologicalComplex (.up ℤ)).map
        ((transpose l E Y).map (PrincipalKoszulStrictReplacement.sourceTowerMap l E Y f))) ≫
        comparisonZQ l E g θ lambda P' =
      comparisonZQ l E g θ lambda P ≫ DerivedCategory.Q.map
        ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f) := by
  have h := congrArg (fun k ↦ DerivedCategory.Q.map k)
    (comparisonZ_naturality l E g θ lambda f)
  simpa only [Functor.map_comp, comparisonZ, comparisonZQ, comparisonKoszulIso,
    comparisonBalancedIso, Functor.mapIso_hom] using h

end WeilConjectures.FinitePullbackStrictTower
