/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.LowerShriekForget
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.Native.Projection.MateAdjunctionChoice
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunctionMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMateIsIso

/-! # The exceptional forget square for extension by zero -/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ Z) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] [QuasiCompact j]

local instance : IsOpenImmersion (Scheme.Hom.geometricFiberMap j (comp_over j
    (Spec (CommRingCat.of k₀)))) :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion) j _ ‹_›

local instance : QuasiCompact (Scheme.Hom.geometricFiberMap j (comp_over j
    (Spec (CommRingCat.of k₀)))) :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @QuasiCompact) j _ ‹_›

/-- The canonical exact forget comparison for extension by zero. -/
def openProjectionAdicForgetIso :
    extensionByZero j ⋙ forgetBoundedConstructibleAdic k₀ l Z ≅
      forgetBoundedConstructibleAdic k₀ l U ⋙ boundedConstructibleAdicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((Functor.mapDerivedCategoryCompForgetIso (IsoAlgebra.mapOfNatIsoCompForgetIso
      (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l j (comp_over j _)))).app
        M.obj)) (fun φ ↦ ObjectProperty.hom_ext _
          ((Functor.mapDerivedCategoryCompForgetIso (IsoAlgebra.mapOfNatIsoCompForgetIso
            (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l j
              (comp_over j _)))).hom.naturality φ.hom))

/-- Deriving the lifted open adjunction preserves its invertible forget mate. -/
theorem isIso_mateEquiv_openProjectionAdicForgetIso (M : WeilComplex k₀ l Z) :
    IsIso ((mateEquiv (extensionByZeroUpperStarAdjunction j)
      (boundedConstructibleAdicOpenImmersionLowerShriekUpperStarAdjunction
        (l := l) (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
      (openProjectionAdicForgetIso k₀ l j).inv).app M) := by
  let jb := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  let a := ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l j
  let b := adicOpenImmersionLowerShriekAdjunction l jb
  let c := IsoAlgebra.mapOfNatIsoCompForgetIso
    (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l j (comp_over j _))
  have : IsIso (mateEquiv a b c.inv).natTrans :=
    IsoAlgebra.isIso_mateEquiv_mapOfNatIsoCompForgetIso_inv _ _ _ _
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have hd := Adjunction.isIso_mateEquiv_mapDerivedCategorySquareIso a b c.symm
  let A := ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction k₀ l j
  let B := b.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (adicUpperStar l jb).rightDerivedFunctorIsoMapDerivedCategory
  have hd' : IsIso (mateEquiv A B
      (Functor.mapDerivedCategoryCompForgetIso c).inv).natTrans := by
    apply isIso_mateEquiv_of_same_left a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction A B
    exact hd
  let ab := extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) j
  let bb := boundedConstructibleAdicOpenImmersionLowerShriekUpperStarAdjunction (l := l) jb
  have hu (K : (DerivedCategory.boundedConstructibleAdic l
      (U ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory) :
      (bb.unit.app K).hom = B.unit.app K.obj := by
    change (ObjectProperty.ι _).map ((B.restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (Iso.refl _) (Iso.refl _)).unit.app K) = _
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp
  have hc : (ab.counit.app M).hom = A.counit.app M.obj := by
    change (ObjectProperty.ι _).map ((A.restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (Iso.refl _) (Iso.refl _)).counit.app M) = _
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp
  have hm : ((mateEquiv ab bb (openProjectionAdicForgetIso k₀ l j).inv).app M).hom =
      (mateEquiv A B (Functor.mapDerivedCategoryCompForgetIso c).inv).app M.obj := by
    simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
      Category.comp_id]
    change (bb.unit.app _).hom ≫ _ ≫ _ = _
    rw [hu, hc]
    rfl
  apply isIso_of_reflects_iso _ (DerivedCategory.boundedConstructibleAdic l
    (U ↘ Spec (CommRingCat.of k₀)).geometricFiber).ι
  change IsIso (((mateEquiv ab bb (openProjectionAdicForgetIso k₀ l j).inv).app M).hom)
  rw [hm]
  infer_instance

end AlgebraicGeometry.WeilComplex
