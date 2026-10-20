/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.ExtendedTruncationMapIso
public import Sheaf.CategoryTheory.SmartTruncationDecalageTower
public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! Applying a left exact functor to all smart cuts of a CE bicomplex.
Source: Stacks Project, Tags 0118, 0156 and 015X.
(blueprint: lem-sp-mapped-smart-truncation-tower).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace CategoryTheory

theorem embeddingUpNat_extend_preservesLimitsOfShape
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (J : Type) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J (ComplexShape.embeddingUpNat.extendFunctor C) := by
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    let e : ComplexShape.embeddingUpNat.extendFunctor C ⋙
        HomologicalComplex.eval C (ComplexShape.up ℤ) (r : ℤ) ≅
        HomologicalComplex.eval C (ComplexShape.up ℕ) r :=
      NatIso.ofComponents (fun K ↦ K.extendXIso ComplexShape.embeddingUpNat rfl)
        (fun f ↦ by
          change (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f (r : ℤ) ≫
            _ = _ ≫ f.f r
          erw [HomologicalComplex.extendMap_f f ComplexShape.embeddingUpNat
            (i := r) (i' := (r : ℤ)) rfl]
          simp)
    exact preservesLimitsOfShape_of_natIso e.symm
  · apply Functor.preservesLimitsOfShape_of_isZero _ ?_ _
    apply Functor.isZero
    intro K
    exact HomologicalComplex.isZero_extend_X K ComplexShape.embeddingUpNat n
      (fun r hr ↦ by change (r : ℤ) = n at hr; omega)

namespace CartanEilenbergPresentation
variable {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
  (G : B ⥤ C) [G.Additive]

/-- First cut the CE bicomplex, then apply G vertically and totalize. -/
noncomputable def mappedSmartTruncationTower
    (I : HomologicalComplex₂ B (.up ℤ) (.up ℕ)) : EInt ⥤ CochainComplex C ℤ :=
  (CochainComplex.extendedTruncationTower I) ⋙ mappedFunctor G ⋙
    HomologicalComplex₂.totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ)

/-- A CE map acts on the mapped smart-cut tower. -/
noncomputable def mappedSmartTruncationTowerMap
    {I J : HomologicalComplex₂ B (.up ℤ) (.up ℕ)} (f : I ⟶ J) :
    mappedSmartTruncationTower G I ⟶ mappedSmartTruncationTower G J :=
  Functor.whiskerRight (CochainComplex.extendedTruncationTowerMap f)
    (mappedFunctor G ⋙ HomologicalComplex₂.totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ))

variable [PreservesFiniteLimits G]

/-- Left exactness moves the mapped functor through all smart horizontal cuts. -/
noncomputable def mappedSmartTruncationTowerIso
    (I : HomologicalComplex₂ B (.up ℤ) (.up ℕ)) :
    mappedSmartTruncationTower G I ≅ ((mappedFunctor G).obj I).smartTruncationTower := by
  let V := G.mapHomologicalComplex (.up ℕ) ⋙ ComplexShape.embeddingUpNat.extendFunctor C
  letI : PreservesFiniteLimits (ComplexShape.embeddingUpNat.extendFunctor C) := by
    constructor
    intro J _ _
    exact embeddingUpNat_extend_preservesLimitsOfShape (C := C) J
  letI : PreservesFiniteLimits V := inferInstance
  exact Functor.isoWhiskerRight (CochainComplex.extendedTruncationMapIso V I)
    (HomologicalComplex₂.totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ))

/-- The normalized smart-cut comparison commutes with every bicomplex map. -/
theorem mappedSmartTruncationTowerIso_naturality
    {I J : HomologicalComplex₂ B (.up ℤ) (.up ℕ)} (f : I ⟶ J) :
    mappedSmartTruncationTowerMap G f ≫ (mappedSmartTruncationTowerIso G J).hom =
      (mappedSmartTruncationTowerIso G I).hom ≫
        HomologicalComplex₂.smartTruncationTowerMap ((mappedFunctor G).map f) := by
  let V := G.mapHomologicalComplex (.up ℕ) ⋙ ComplexShape.embeddingUpNat.extendFunctor C
  let : PreservesFiniteLimits (ComplexShape.embeddingUpNat.extendFunctor C) := by
    constructor
    intro J _ _
    exact embeddingUpNat_extend_preservesLimitsOfShape (C := C) J
  let : PreservesFiniteLimits V := inferInstance
  apply NatTrans.ext
  funext a
  change HomologicalComplex₂.total.map _ (.up ℤ) ≫
      HomologicalComplex₂.total.map _ (.up ℤ) =
    HomologicalComplex₂.total.map _ (.up ℤ) ≫ HomologicalComplex₂.total.map _ (.up ℤ)
  rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
  exact congrArg (fun u ↦ HomologicalComplex₂.total.map u (.up ℤ))
    (NatTrans.congr_app (CochainComplex.extendedTruncationMapIso_naturality V f) a)

end CartanEilenbergPresentation
end CategoryTheory
