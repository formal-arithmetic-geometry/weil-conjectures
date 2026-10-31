/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTowerRealizationComparisons
import all WeilConjectures.CategoryTheory.UnboundedExactAdjunctionSquare
import WeilConjectures.AlgebraicGeometry.RingedOpenScalarLimitCoherence

/-! Coherence of exact functors with the constant-diagram mate. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint limit
namespace CategoryTheory

variable {A B C D : Type*}
  [Category A] [Abelian A] [HasLimits A] [HasDerivedCategory A]
  [Category B] [Abelian B] [HasLimits B] [HasDerivedCategory B]
  [Category C] [Abelian C] [HasLimits C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasLimits D] [HasDerivedCategory D]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]

private abbrev tower {E E' : Type*} [Category E] [Category E'] (V : E ⥤ E') :=
  (Functor.whiskeringRight ℕᵒᵖ E E').obj V

omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)] in
private theorem constantSquare (e : F ⋙ G ≅ H ⋙ K) (X : DerivedCategory A) :
    (Functor.const ℕᵒᵖ : D ⥤ _).mapDerivedCategory.map
        ((cbcDerivedSquare F G H K e).inv.app X) ≫
      (UnboundedExactTower.constantInterchange G).inv.app (F.mapDerivedCategory.obj X) ≫
      (tower G).mapDerivedCategory.map
        ((UnboundedExactTower.constantInterchange F).inv.app X) =
    (UnboundedExactTower.constantInterchange K).inv.app (H.mapDerivedCategory.obj X) ≫
      (tower K).mapDerivedCategory.map
        ((UnboundedExactTower.constantInterchange H).inv.app X) ≫
      (cbcDerivedTowerSquare F G H K e).inv.app
        ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj X) := by
  have h := UnboundedExactTower.constant_cube H G F K e X
  have he :
      (tower G).mapDerivedCategory.mapIso ((UnboundedExactTower.constantInterchange F).app X) ≪≫
        (UnboundedExactTower.constantInterchange G).app (F.mapDerivedCategory.obj X) ≪≫
        (Functor.const ℕᵒᵖ : D ⥤ _).mapDerivedCategory.mapIso
          ((cbcDerivedSquare F G H K e).app X) =
      (cbcDerivedTowerSquare F G H K e).app
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj X) ≪≫
        (tower K).mapDerivedCategory.mapIso ((UnboundedExactTower.constantInterchange H).app X) ≪≫
        (UnboundedExactTower.constantInterchange K).app (H.mapDerivedCategory.obj X) := by
    apply Iso.ext
    exact h
  have hi := congrArg (fun z ↦ z.inv) he
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hi

private def constAdj {E : Type*} [Category E] [Abelian E] [HasLimits E]
    [HasDerivedCategory E] [HasDerivedCategory (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)] :=
  letI : (lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive :=
    Functor.additive_of_preserves_binary_products _
  (constLimAdj : (Functor.const ℕᵒᵖ : E ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction

private def limitMap {E E' : Type*} [Category E] [Abelian E] [HasLimits E]
    [Category E'] [Abelian E'] [HasLimits E']
    [HasDerivedCategory E] [HasDerivedCategory E']
    [HasDerivedCategory (ℕᵒᵖ ⥤ E)] [HasDerivedCategory (ℕᵒᵖ ⥤ E')]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E')]
    (V : E ⥤ E') [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V] :=
  letI : (lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (lim : (ℕᵒᵖ ⥤ E') ⥤ E').Additive :=
    Functor.additive_of_preserves_binary_products _
  (mateEquiv (constAdj (E := E)) (constAdj (E := E'))
    (TwoSquare.mk _ _ _ _ (UnboundedExactTower.constantInterchange V).inv)).natTrans

attribute [local instance] Functor.additive_of_preserves_binary_products
omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D] in
private theorem limitSquare (e : F ⋙ G ≅ H ⋙ K)
    (X : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    G.mapDerivedCategory.map ((limitMap F).app X) ≫
        (limitMap G).app ((tower F).mapDerivedCategory.obj X) ≫
        lim.rightDerivedFunctor.map ((cbcDerivedTowerSquare F G H K e).hom.app X) =
      (cbcDerivedSquare F G H K e).hom.app (lim.rightDerivedFunctor.obj X) ≫
        K.mapDerivedCategory.map ((limitMap H).app X) ≫
        (limitMap K).app ((tower H).mapDerivedCategory.obj X) := by
  exact exchangeMate_cube (constAdj (E := A)) (constAdj (E := B))
    (constAdj (E := C)) (constAdj (E := D))
    H.mapDerivedCategory (tower H).mapDerivedCategory
    G.mapDerivedCategory (tower G).mapDerivedCategory
    (UnboundedExactTower.constantInterchange H) (cbcDerivedSquare F G H K e)
    (cbcDerivedTowerSquare F G H K e) (UnboundedExactTower.constantInterchange G)
    (UnboundedExactTower.constantInterchange F).inv
    (UnboundedExactTower.constantInterchange K).inv (constantSquare F G H K e) X

end CategoryTheory

namespace AlgebraicGeometry.Scheme
universe t
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)


private theorem realizationLimitMap_eq {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    cbcRealizationLimitMap F = CategoryTheory.limitMap F := by
  have hi : Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F).symm =
      (Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F)).symm :=
    Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
  have hc : (cbcRealizationConst F).hom =
      (UnboundedExactTower.constantInterchange F).inv := by
    simp only [cbcRealizationConst, UnboundedExactTower.constantInterchange, hi,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  unfold cbcRealizationLimitMap CategoryTheory.limitMap
  rw [hc]
  rfl


/-- Scalar restriction and open extension commute with their constant-diagram limit mates.
Source: Stacks Tags 05S7 and 07A7.
(blueprint: lem-cbc-completed-open-scalar-limit-square).
Proof: localize the degreewise constant-diagram cube for the specified scalar/open
comparison, then apply the adjunction mate cube identity to the four limit adjunctions. -/
theorem completedOpenScalarLimitSquare {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j]
    (X : DerivedCategory (exchangeTowers U (d.completedRing U))) :
    (cbcRealizationRes d T).mapDerivedCategory.map
        ((cbcRealizationLimitMap (cbcOpenShriek d j inferInstance)).app X) ≫
      (cbcRealizationResLimit d T).hom.app ((cbcRealizationJ d j).obj X) ≫
      (completedRlim T (exchangeConstantRing T A)).map
        ((cbcRealizationTowerScalarOpen d j).hom.app X) =
    (cbcRealizationDerivedScalarOpen d j).hom.app
        ((completedRlim U (d.completedRing U)).obj X) ≫
      (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory.map
        ((cbcRealizationResLimit d U).hom.app X) ≫
      (cbcRealizationOpenLimit d j).hom.app ((exchangeTowerRes d U).obj X) := by
  have ht : cbcRealizationTowerScalarOpen d j =
      cbcDerivedTowerSquare (cbcOpenShriek d j inferInstance) (cbcRealizationRes d T)
        (cbcRealizationRes d U) (ProEtale.StrictTower.moduleJ A j)
        (cbcRealizationScalarOpen d j) := by
    unfold cbcRealizationTowerScalarOpen cbcDerivedTowerSquare
      CategoryTheory.NormalizedLimitSquare.towerSquare
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
      Functor.whiskeringRightObjCompIso, Iso.refl_symm,
      Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
    erw [Functor.mapDerivedCategoryNatIso_refl, Functor.mapDerivedCategoryNatIso_refl]
    simp only [Category.id_comp]
    rfl
  have := cbcOpenShriek_additive d j inferInstance
  have := cbcOpenShriek_finiteLimits d j inferInstance
  have := cbcOpenShriek_finiteColimits d j inferInstance
  have hh := CategoryTheory.limitSquare
    (A := reductionModules U (d.completedRing U))
    (B := reductionModules T (d.completedRing T))
    (C := reductionModules U (exchangeConstantRing U A))
    (D := reductionModules T (exchangeConstantRing T A))
    (cbcOpenShriek d j inferInstance)
    (cbcRealizationRes d T) (cbcRealizationRes d U) (ProEtale.StrictTower.moduleJ A j)
    (cbcRealizationScalarOpen d j) X
  dsimp only [completedRlim, completedTowerLimit] at *
  simpa only [cbcRealizationResLimit, cbcRealizationOpenLimit, asIso_hom,
    realizationLimitMap_eq, ht, cbcRealizationDerivedScalarOpen, cbcDerivedSquare,
    Functor.mapDerivedCategorySquareIso, Category.assoc, cbcRealizationJ,
    exchangeTowerRes, exchangeTowerModuleRes, cbcRealizationRes, cbcTowerDerived,
    ProEtale.StrictTower.J, ProEtale.StrictTower.towerJ, cbcRealizationTowerJ,
    CategoryTheory.tower, ProEtale.StrictTower.Modules, ProEtale.StrictTower.coefficients,
    exchangeConstantRing, adicLisseConstantRing, pbcModules, proEtaleRingModules,
    adicLisseForget, reductionModules, reductionModuleRing,
    pbcAdicCompletion, AdicCoefficientDatum.completedRing, AdicCoefficients.completedRing,
    completedReductionCoefficient, reductionCoefficientSystem] using hh

end AlgebraicGeometry.Scheme
