/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageConeTowerNormalizationDefs

/-! Derived mate and K-injective unit normalization for the direct-image cone.

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (2).
(blueprint: lem-weil-pbc-direct-image-cone-tower-derived-mate-normalization).

The derived mate identity is expanded with `unit_mateEquiv` and the naturality of
the right-derived units. The localization equation `IsPullReduction` identifies
the strict pullback comparison, and the K-injective object comparison rewrites the
remaining module unit. The tower unit is retained as a morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem derivedCounitOnComplex
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R) (I : CochainComplex D ℤ) :
    L.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ I) ≫
        a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient D (.up ℤ)).obj I)
  change L.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app _) ≫
    a.mapDerivedCategoryRightDerivedAdjunction.counit.app _ =
    L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj I)) ≫ _ at h
  simp only [Functor.rightDerivedFunctorUnitQ, Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_counit_app_quotient, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.map_comp, Category.assoc] at h ⊢
  simp only [Quotient.lift.isLift_hom] at h ⊢
  repeat erw [CategoryTheory.Functor.map_id] at h
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp] at h
  repeat erw [Category.id_comp]
  exact h

set_option maxHeartbeats 800000 in
-- Rewriting the composed localization comparisons exceeds the default heartbeat budget.
/-- A strict comparison identified with the canonical ordinary mate has the
K-injective right-derived normalization.
Source: the localized mate and K-injective unit calculation in proof (2) of
`lem-weil-pbc-direct-image-cone-tower-k-injective-normalization`.

The proof applies the unit-mate identity to `pullReduction`, uses its defining
localization equation and right-derived-unit naturality, and then rewrites the
module unit on a K-injective representative by `rightDerivedFunctorUnitQ_eq`.
-/
theorem strictDirectImageConeTower_derived_mate_normalization
    (e : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)
          (ComplexShape.up ℤ) ⋙ strictRed l E Y)
    (hm : e.inv =
      (mateEquiv
        ((CondensedRing.upperStarLowerStarAdjunction
          (DerivedNakayama.integerRing l E) f).mapHomologicalComplex (.up ℤ))
        (((CondensedRing.upperStarLowerStarAdjunction
          (DerivedNakayama.integerRing l E) f).whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ))
        (TwoSquare.mk _ _ _ _ (strictPullReduction l E f).hom)).natTrans) :
    IsKInjectiveDirectImageNormalization l E f e := by
  intro I hI
  let a := CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f
  let b := a.whiskerRight ℕᵒᵖ
  let R := CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f
  let J := (R.mapHomologicalComplex (.up ℤ)).obj I
  have hc := derivedCounitOnComplex a I
  have ht := derivedCounitOnComplex b ((strictRed l E X).obj I)
  have hn := (redFactors l E X).hom.naturality
    ((a.mapHomologicalComplex (.up ℤ)).counit.app I)
  have hp := (pullReduction_existsUnique l E f).exists.choose_spec J
  have hm' := mateEquiv_counit (a.mapHomologicalComplex (.up ℤ))
    (b.mapHomologicalComplex (.up ℤ))
    (TwoSquare.mk _ _ _ _ (strictPullReduction l E f).hom) I
  change ((pull l E f).mapHomologicalComplex (.up ℤ)).map
    (((mateEquiv (a.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ)))
      (TwoSquare.mk _ _ _ _ (strictPullReduction l E f).hom)).natTrans.app I) ≫
      (b.mapHomologicalComplex (.up ℤ)).counit.app ((strictRed l E X).obj I) =
    (strictPullReduction l E f).hom.app J ≫
      (strictRed l E X).map ((a.mapHomologicalComplex (.up ℤ)).counit.app I) at hm'
  rw [← hm] at hm'
  apply ((towerAdjunction l E f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [(towerAdjunction l E f).counit.naturality]
  have hd := mateEquiv_counit (moduleAdjunction l E f) (towerAdjunction l E f)
    (TwoSquare.mk _ _ _ _ (pullReduction l E f).hom) (DerivedCategory.Q.obj I)
  erw [reassoc_of% hd]
  erw [reassoc_of% (pullReduction l E f).hom.naturality (R.rightDerivedFunctorUnitQ I)]
  simp only [Functor.id_map]
  rw [← (red l E X).map_comp_assoc]
  erw [hc]
  simp only [Functor.map_comp, Category.assoc]
  erw [hn]
  rw [← cancel_epi ((dpull l E f).map ((redFactors l E Y).inv.app J))]
  erw [reassoc_of% hp]
  erw [ht]
  erw [reassoc_of% (pull l E f).mapDerivedCategoryFactors.hom.naturality (e.inv.app I)]
  simp only [Functor.comp_map, Functor.comp_obj, ← Functor.map_comp]
  rw [hm']
  dsimp only [J, R]
  rw [← (dpull l E f).map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
