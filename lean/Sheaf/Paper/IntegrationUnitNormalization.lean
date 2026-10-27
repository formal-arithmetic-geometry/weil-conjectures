/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegrationTransposeCompositionData
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Unit normalization of compact-support integration

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-integration-unit-normalization).
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u u'

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem swap_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) (P Q : D ⥤ C) (e : P ≅ Q) (unit : P.obj (𝟙_ D) ≅ 𝟙_ C)
    (π : ∀ M K, F.obj M ⊗ K ⟶ F.obj (M ⊗ P.obj K))
    (hu : ∀ M, π M (𝟙_ D) ≫
      F.map (M ◁ unit.hom ≫ (ρ_ M).hom) = (ρ_ (F.obj M)).hom)
    (M : C) :
    (β_ (𝟙_ D) (F.obj M)).hom ≫ π M (𝟙_ D) ≫
        F.map (M ◁ e.hom.app (𝟙_ D)) ≫
        F.map (β_ (Q.obj (𝟙_ D)) M).inv ≫
        F.map ((e.inv.app (𝟙_ D) ≫ unit.hom) ▷ M ≫ (λ_ M).hom) =
      (λ_ (F.obj M)).hom := by
  have h : M ◁ e.hom.app (𝟙_ D) ≫ (β_ (Q.obj (𝟙_ D)) M).inv ≫
      (e.inv.app (𝟙_ D) ≫ unit.hom) ▷ M ≫ (λ_ M).hom =
      M ◁ unit.hom ≫ (ρ_ M).hom := by
    rw [BraidedCategory.braiding_inv_naturality_right_assoc]
    rw [← comp_whiskerRight_assoc]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← BraidedCategory.braiding_inv_naturality_right_assoc]
    simp
  simp only [← F.map_comp]
  rw [h, hu]
  simp

private theorem projection_unit_general
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {V T : Scheme.{u}} (f : V ⟶ T) [HasCompactification f]
    (M : DerivedCategory (Sheaf V.smallEtaleTopology B)) :
    IntegrationComposition.integrationProjection B f M (𝟙_ _) ≫
      (rightDerivedLowerShriek B f).map
        (IntegrationComposition.integrationUnitObjectIso B f M).hom =
      (derivedTensorLeftUnitor B T ((rightDerivedLowerShriek B f).obj M)).hom := by
  unfold IntegrationComposition.integrationProjection
    IntegrationComposition.integrationUnitObjectIso
  let := _root_.DerivedCategory.braidedCategory' (Sheaf V.smallEtaleTopology B)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf T.smallEtaleTopology B)
  have hs (K N : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
      ((derivedTensorSymmetry B T).hom.app K).app N = (β_ K N).hom := rfl
  have hs' (K N : DerivedCategory (Sheaf V.smallEtaleTopology B)) :
      ((derivedTensorSymmetry B V).inv.app K).app N = (β_ K N).inv := rfl
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    NatTrans.comp_app, hs, hs', derivedTensor_obj_map, derivedTensor_map_app,
    derivedTensorLeftUnitor, comp_whiskerRight, Functor.map_comp, Category.assoc] using
    swap_unit (rightDerivedLowerShriek B f) _ _
      (leftDerivedUpperStarIsoMapDerivedCategory B f) (leftDerivedUpperStarUnitIso B f)
      (fun M K ↦ ((projectionMap B f).app M).app K)
      (projectionMap_rightUnitality B f) M


namespace IntegrationComposition

variable {A : Type (u + 1)} [CommRing A] {X Y Z : Scheme.{u}}

private theorem projection_eq (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    compactSupportProjectionMap A f W K =
      integrationProjection (ModuleCat.{u + 1} A) f W K := by
  unfold integrationProjection
  rfl

/-- Projection at the unit agrees with the exact inverse-image unit identification.
Source: cor-pur-vector-bundle-purity.proof.md paragraph 2, node proof steps 1--2.
(blueprint: lem-pur-integration-unit-normalization).

Proof: Expand the coefficient-first projection into symmetry, the ordinary projection,
exact-pullback comparison and inverse symmetry. Naturality of inverse symmetry moves
this last comparison past the exact unit map. The exact comparison and its inverse cancel.
The remaining ordinary projection followed by its pullback unit map is the right unitor,
by projectionMap_rightUnitality. The outer braiding converts it to the left unitor. -/
theorem integration_unit_normalization (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X) :
    compactSupportProjectionMap A f W (𝟙_ _) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (unitObjectIso f W).hom =
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W)).hom := by
  exact (congrArg (fun p ↦ p ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (unitObjectIso f W).hom)
    (projection_eq f W (𝟙_ _))).trans
      (projection_unit_general (ModuleCat.{u + 1} A) f W)

end IntegrationComposition

end AlgebraicGeometry.Etale
