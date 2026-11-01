/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionChain
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletionChainNormalization

/-! # Naturality of tensor completion for a strict tower square

Source: Bhatt--Scholze 3.4.10; naturality of the actual Roos augmentation.
(blueprint: lem-coef-rational-verdier-completion-chain-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

attribute [local implicit_reducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsTensorComplexFunctor
  IntegralAmbient.tensorTower
  IntegralOnSlice.Site IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring
  PurCompactSupport.completed
attribute [local irreducible] IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOperationsTensorTowerFunctor

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem unit_square
    {C B : Type*} [Category* C] [Category* B] (R : B ⥤ C)
    {A A' : C} {U U' V V' : B}
    (s : A ⟶ A') (η : A ⟶ R.obj U) (η' : A' ⟶ R.obj U')
    (t : U ⟶ U') (b : U ⟶ V) (b' : U' ⟶ V') (a : V ⟶ V')
    (hn : s ≫ η' = η ≫ R.map t) (ht : t ≫ b' = b ≫ a) :
    s ≫ (η' ≫ R.map b') = (η ≫ R.map b) ≫ R.map a := by
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp, ht,
    R.map_comp, ← Category.assoc]

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] in
/-- A strict square before Roos induces the corresponding completion-chain square.
Source: Bhatt--Scholze 3.4.10, Stacks 08TC.
(blueprint: lem-coef-rational-verdier-completion-chain-naturality).
Proof: identify completion with the native augmentation, then combine naturality
of roosUnit with functoriality of Roos and the supplied strict tower equation.
Because this uses the actual Roos functor, both mapping-fibre coordinates and
its differential are included in the resulting square. -/
theorem completion_natural_of_tower_square
    (P Q : CochainComplex (integralTowerModules l E X) ℤ)
    (s : (constructibleTensorTotal l E X).obj (P, Q) ⟶
      (constructibleTensorTotal l E X).obj (Q, P))
    (a : (integralOperationsTensorTowerFunctor l E X).obj (P, Q) ⟶
      (integralOperationsTensorTowerFunctor l E X).obj (Q, P))
    (ha : (IntegralOnSlice.tower l E X none).map s ≫
        (IntegralAmbient.tensorTowerIso l E X).hom.app (Q, P) =
      (IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q) ≫ a) :
    s ≫ (completionChain D l hl X E).app (Q, P) =
      (completionChain D l hl X E).app (P, Q) ≫ integralOperationsRoosFunctor.map a := by
  rw [completionChain_eq_native D l hl X E]
  rw [ConstructibleTensorModel.tensorCompletionChain_app,
    ConstructibleTensorModel.tensorCompletionChain_app]
  unfold ConstructibleTensorModel.tensorCompletionUnitMap IntegralAmbient.tensorOperationUnit
  have hn := ConstructibleTensorModel.tensorRoosUnit_natural l E X s
  exact unit_square integralOperationsRoosFunctor s _ _ _ _ _ a hn ha

end WeilConjectures.RationalVerdier
