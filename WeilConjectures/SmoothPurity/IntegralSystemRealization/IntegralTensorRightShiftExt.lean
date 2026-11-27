/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorShiftProperties
import all WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorLeftShiftUnique

/-! # Extensionality of normalized completed right shifts

## Implementation details

The argument is the first-slot one of `integralTensorLeftShift_existsUnique`: a normalized
comparison is determined on good models by its finite formula and its cone formula, and both
of these are determined by the values on tensor generators.

## References

* Stacks Project, Tags 011G, 014E, 06YU and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory AlgebraicGeometry Opposite
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  SheafOfModules.monoidalCategory
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem rightFormula_ext (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ)
    (α β : (integralOperationsTensorTowerFunctor l E W).obj (P, Q⟦r⟧) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙ shiftFunctor _ r)
    (hα : integralCompletedTensorFiniteShiftFormula l E W P Q r α)
    (hβ : integralCompletedTensorFiniteShiftFormula l E W P Q r β) : α = β := by
  apply Iso.ext
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  let π := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n.unop)
  let := completedProjection_locallySurjective l E W n.unop
  let P' := (unrestrictedIntegralFiniteComplex l E W n.unop).obj P
  let Q' := (unrestrictedIntegralFiniteComplex l E W n.unop).obj (Q⟦r⟧)
  let T := MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n.unop)
  let X := (CochainComplex.mapBifunctor P' Q' T).X k
  let Y := (CochainComplex.mapBifunctor P'
    ((unrestrictedIntegralFiniteComplex l E W n.unop).obj Q) T).X (k + r)
  let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    π.hom Y.isSheaf (M₁ := X.val)
  apply hom_ext_of_full (SheafOfModules.restrictScalars π) (X := X) (Y := Y)
  · intro φ
    refine ⟨⟨e.symm φ.val⟩, ?_⟩
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply _
  · intro f g hf hg
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := P') (K₂ := Q') (F := T) (c := .up ℤ)
    intro i j hij
    apply finitePure_ext l E W n.unop
    intro U x y
    change i + j = k at hij
    subst k
    have h := (hα n.unop i j U x y).trans (hβ n.unop i j U x y).symm
    rw [← hf, ← hg] at h
    exact h

attribute [local irreducible] integralCompletedTensorComparison
  integralOperationsTensorTowerFunctor integralCompletedTensorFiniteShiftFormula
  completedTensorShiftConeFormula completedTensorShiftRoosIso
attribute [local instance 3000] integralOperationsCommHasDerivedCategory

/-- Equality of completed right-slot comparisons with the same representative normalization. -/
theorem integralTensorRightShift_ext (W : Scheme.{u}) (r : ℤ)
    (σ τ : completedTensorShiftSecond (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r)
    (hσ : integralCompletedTensorRightShiftProperty l E W r σ)
    (hτ : integralCompletedTensorRightShiftProperty l E W r τ) : σ = τ := by
  let L := integralOperationsGoodLocalization l E W
  let G := integralCompletedTensor l E W
  let S := shiftFunctor (Integral l E W) r
  let T := integralOperationsTensorTowerFunctor l E W
  let ε := integralCompletedTensorComparison l E W
  exact iso_ext_normalized (L.prod L)
    (fun Y ↦ by
      obtain ⟨P, ⟨eP⟩⟩ := goodModelRepresentative l E W Y.1
      obtain ⟨Q, ⟨eQ⟩⟩ := goodModelRepresentative l E W Y.2
      exact ⟨(P, Q), ⟨eP.prod eQ⟩⟩)
    (F := completedTensorShiftSecond (Integral l E W) r ⋙ G) (G := G ⋙ S)
    (fun X ↦ G.obj (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj (X.2.obj⟦r⟧)))
    (fun X ↦ S.obj ((integralOperationsTensorOnGood l E W).obj X))
    (fun X ↦ G.map (𝟙 (DerivedCategory.Q.obj X.1.obj),
      (DerivedCategory.Q.commShiftIso r).hom.app X.2.obj))
    (fun X ↦ by
      have : IsIso (show (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj (X.2.obj⟦r⟧)) ⟶
          (DerivedCategory.Q.obj X.1.obj, (DerivedCategory.Q.obj X.2.obj)⟦r⟧) from
          (𝟙 _, (DerivedCategory.Q.commShiftIso r).hom.app X.2.obj)) :=
        (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
      exact @Functor.map_isIso _ _ _ _ _ _ G _ this)
    (fun X ↦ S.map (ε.hom.app X)) (fun _ ↦ inferInstance)
    (fun X ↦ integralOperationsGoodComplex l E W (X.2.obj⟦r⟧))
    (fun X ↦ integralCompletedTensorFiniteShiftFormula l E W X.1.obj X.2.obj r)
    (fun X ↦ completedTensorShiftConeFormula
      (T.obj (X.1.obj, X.2.obj)) (T.obj (X.1.obj, X.2.obj⟦r⟧)) r)
    (fun X hQ δ ↦ ε.hom.app (X.1, ⟨X.2.obj⟦r⟧, hQ⟩) ≫ DerivedCategory.Q.map
      (completedTensorShiftRoosIso (T.obj (X.1.obj, X.2.obj))
        (T.obj (X.1.obj, X.2.obj⟦r⟧)) r δ).hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        ((integralOperationsTensorComplexFunctor l E W).obj (X.1.obj, X.2.obj)))
    (fun X ↦ rightFormula_ext l E W X.1.obj X.2.obj r) (fun _ ↦ coneFormula_ext _ _ r)
    σ τ (fun X ↦ hσ X.1 X.2) (fun X ↦ hτ X.1 X.2)

end WeilConjectures.IntegralSystemRealization
