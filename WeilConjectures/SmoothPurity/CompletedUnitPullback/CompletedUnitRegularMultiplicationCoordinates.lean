/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularMultiplication
import WeilConjectures.SmoothPurity.CoefficientClosedStructure.CoefficientClosedTensorComparison
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import all WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification

/-! # Regular coefficient multiplication and the normalized unit coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] WeilConjectures.coefficientSequenceInternalHom
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- Naturality alone controls multiplication for the unit comparison built from both unitors.
private theorem comparison_unit_formula
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S T : CoefficientClosedStructure H) (O : D)
    (uT : T.monoidal.tensorUnit ≅ O) :
    let c := CoefficientClosedStructure.comparison S T
    let d := (T.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
      (c.app (S.monoidal.tensorUnit, T.monoidal.tensorUnit)).symm ≪≫
      S.monoidal.leftUnitor T.monoidal.tensorUnit
    let uS := d ≪≫ uT
    (S.monoidal.leftUnitor S.monoidal.tensorUnit).hom ≫ uS.hom =
      S.tensor.map (Prod.mkHom uS.hom uS.hom) ≫
        c.hom.app (O, O) ≫ T.tensor.map (Prod.mkHom uT.inv (𝟙 O)) ≫
        (T.monoidal.leftUnitor O).hom := by
  dsimp only
  let c := CoefficientClosedStructure.comparison S T
  let d := (T.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
      (c.app (S.monoidal.tensorUnit, T.monoidal.tensorUnit)).symm ≪≫
      S.monoidal.leftUnitor T.monoidal.tensorUnit
  let uS := d ≪≫ uT
  change (S.monoidal.leftUnitor S.monoidal.tensorUnit).hom ≫ uS.hom = _
  have hd : c.hom.app (S.monoidal.tensorUnit, T.monoidal.tensorUnit) ≫
      (T.monoidal.rightUnitor S.monoidal.tensorUnit).hom ≫ d.hom =
        (S.monoidal.leftUnitor T.monoidal.tensorUnit).hom := by
    simp [d]
  have htl : T.tensor.map (Prod.mkHom (𝟙 _) uT.hom) ≫
      (T.monoidal.leftUnitor O).hom =
        (T.monoidal.leftUnitor T.monoidal.tensorUnit).hom ≫ uT.hom := by
    let _ := T.monoidal
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.id_tensorHom] using MonoidalCategory.leftUnitor_naturality uT.hom
  have htr : T.tensor.map (Prod.mkHom d.hom (𝟙 _)) ≫
      (T.monoidal.leftUnitor T.monoidal.tensorUnit).hom =
        (T.monoidal.rightUnitor S.monoidal.tensorUnit).hom ≫ d.hom := by
    let _ := T.monoidal
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.tensorHom_id, MonoidalCategory.unitors_equal] using
      MonoidalCategory.rightUnitor_naturality d.hom
  have ht : T.tensor.map (Prod.mkHom uS.hom uS.hom) ≫
      T.tensor.map (Prod.mkHom uT.inv (𝟙 O)) ≫ (T.monoidal.leftUnitor O).hom =
        T.tensor.map (Prod.mkHom (𝟙 S.monoidal.tensorUnit) d.hom) ≫
          (T.monoidal.rightUnitor S.monoidal.tensorUnit).hom ≫ uS.hom := by
    calc
      _ = T.tensor.map (Prod.mkHom (𝟙 S.monoidal.tensorUnit) d.hom) ≫
          T.tensor.map (Prod.mkHom d.hom (𝟙 T.monoidal.tensorUnit)) ≫
          T.tensor.map (Prod.mkHom (𝟙 T.monoidal.tensorUnit) uT.hom) ≫
          (T.monoidal.leftUnitor O).hom := by
        simp only [← Functor.map_comp_assoc, prod_comp, uS, Iso.trans_hom,
          Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
      _ = _ := by rw [htl, reassoc_of% htr]; rfl
  have hsl : S.tensor.map (Prod.mkHom (𝟙 _) d.hom) ≫
      (S.monoidal.leftUnitor T.monoidal.tensorUnit).hom =
        (S.monoidal.leftUnitor S.monoidal.tensorUnit).hom ≫ d.hom := by
    let _ := S.monoidal
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.id_tensorHom] using MonoidalCategory.leftUnitor_naturality d.hom
  symm
  rw [c.hom.naturality_assoc, ht, ← c.hom.naturality_assoc]
  change S.tensor.map (Prod.mkHom (𝟙 _) d.hom) ≫
    c.hom.app (S.monoidal.tensorUnit, T.monoidal.tensorUnit) ≫
      (T.monoidal.rightUnitor S.monoidal.tensorUnit).hom ≫ d.hom ≫ uT.hom = _
  rw [reassoc_of% hd, reassoc_of% hsl]
  rfl

set_option maxHeartbeats 800000 in
-- Normalizing the concrete derived tensor involves large universe-polymorphic instances.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.coefficientSequenceEssentiallySmall in
private theorem regular_model_comparison (W : Scheme.{u})
    (S T : CoefficientClosedStructure (coefficientSequenceInternalHom l E W))
    (s : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) S)
    (t : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) T) :
    (CoefficientClosedStructure.comparison S T).hom.app
        (systemObject l E W, systemObject l E W) ≫
      (t.iso _ _ T _ _ (regularUnitComplex_kFlat l E W)
        (regularUnitComplex_kFlat l E W)).inv =
      (s.iso _ _ S _ _ (regularUnitComplex_kFlat l E W)
        (regularUnitComplex_kFlat l E W)).inv := by
  let J := coefficientSequenceTopology (Scheme.ProEt.topology W)
  let R := coefficientSequenceCommRingSheaf l E W
  let P := ringedTensorUnitComplex.{u + 1, u, u} J R
  let I := (coefficientTotalTensor.{u, u + 1, u} J R).obj (P, P)
  obtain ⟨g, hg, _⟩ := coefficientCochainTensorCurry_exists J R P P I (𝟙 I)
  have hs := coefficientTensorCurry_normalize.{u, u + 1, u, u + 2} J R
    S s P P I (regularUnitComplex_kFlat l E W) (regularUnitComplex_kFlat l E W)
    (𝟙 I) g hg
  have ht := coefficientTensorCurry_normalize.{u, u + 1, u, u + 2} J R
    T t P P I (regularUnitComplex_kFlat l E W) (regularUnitComplex_kFlat l E W)
    (𝟙 I) g hg
  have hid := (DerivedCategory.Q (C := coefficientSequenceModules.{u, u} l E W)).map_id I
  erw [hid, Category.comp_id] at hs ht
  apply (S.transpose _ _ _).injective
  rw [CoefficientClosedStructure.comparison_transpose, ← ht, ← hs]
  exact ((T.transpose _ _ _).apply_symm_apply _).trans
    ((S.transpose _ _ _).apply_symm_apply _).symm

set_option maxHeartbeats 800000 in
-- The concrete derived-site comparisons require a larger elaboration budget.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.coefficientSequenceEssentiallySmall in
/-- The closed-unit coordinate comparison preserves the actual regular multiplication.
Source: Stacks 07A4 and 08J9; the closed tensor-Hom comparison used in
`tensorSystemUnit`, and the ring-unit calculation in purity transport Step 2.
(blueprint: lem-pur-completed-unit-regular-multiplication-coordinates).

Proof: compare the two tensor-Hom left adjoints through their canonical adjunction
comparison. Its unit identity and the normalized representative uncurrying equation
identify the total-tensor comparisons. Apply this at the regular K-flat unit pair.
The native derived unitor model is coefficient multiplication on the degree-zero
pure-tensor generators. Transport this formula through the left-adjoint comparison.
Naturality of the unitors cancels the intervening right unitor in tensorSystemUnit;
the resulting identity is precisely the multiplication equation below. This is an
absolute calculation on one scheme, with no morphism or integral reconstruction. -/
theorem regularSystemMultiplication_coordinates (W : Scheme.{u}) :
    ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit).hom ≫
        (tensorSystemUnit l E W).hom =
      (pullbackTensorCalculus l E W).systemClosed.tensor.map
        (Prod.mkHom (tensorSystemUnit l E W).hom (tensorSystemUnit l E W).hom) ≫
        (regularSystemMultiplication l E W).hom := by
  let J := coefficientSequenceTopology (Scheme.ProEt.topology W)
  let R := coefficientSequenceCommRingSheaf l E W
  let P := ringedTensorUnitComplex.{u + 1, u, u} J R
  let S := (pullbackTensorCalculus l E W).systemClosed
  let T := (pullbackTensorCalculus l E W).systemTensorModel
  let h := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2} J R
  let S₀ := h.choose
  let T₀ := h.choose_spec.choose
  let β₀ := h.choose_spec.choose_spec.choose
  let h₀ := h.choose_spec.choose_spec.choose_spec.some
  let r := T.iso J R S P P (regularUnitComplex_kFlat l E W)
    (regularUnitComplex_kFlat l E W)
  let r₀ := T₀.iso J R S₀ P P (regularUnitComplex_kFlat l E W)
    (regularUnitComplex_kFlat l E W)
  let c := CoefficientClosedStructure.comparison S S₀
  have hcmp : c.hom.app (systemObject l E W, systemObject l E W) ≫ r₀.inv = r.inv :=
    regular_model_comparison l E W S S₀ T T₀
  have hu := RingedKFlatModel.leftUnitor_model_native.{u + 1, u, u, u + 2}
    J R S₀ T₀ β₀ h₀ P (regularUnitComplex_kFlat l E W)
  have hb := h₀.tensorIso_both P P (regularUnitComplex_kFlat l E W)
    (regularUnitComplex_kFlat l E W)
  rw [show h₀.tensorIso P P (Or.inr (regularUnitComplex_kFlat l E W)) = r₀ by
    exact hb] at hu
  change r₀.hom ≫ S₀.tensor.map (Prod.mkHom h₀.unitIso.inv (𝟙 (systemObject l E W))) ≫
      (S₀.monoidal.leftUnitor (systemObject l E W)).hom =
      DerivedCategory.Q.map (regularUnitComplex_multiplication l E W).hom at hu
  have hmul : r₀.inv ≫ DerivedCategory.Q.map
      (regularUnitComplex_multiplication l E W).hom =
      S₀.tensor.map (Prod.mkHom h₀.unitIso.inv (𝟙 (systemObject l E W))) ≫
        (S₀.monoidal.leftUnitor (systemObject l E W)).hom := by
    rw [← hu, Iso.inv_hom_id_assoc]
  have he : tensorSystemUnit l E W =
      (S₀.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
        (c.app (S.monoidal.tensorUnit, S₀.monoidal.tensorUnit)).symm ≪≫
        S.monoidal.leftUnitor S₀.monoidal.tensorUnit ≪≫ h₀.unitIso := by
    dsimp only [tensorSystemUnit, c, CoefficientClosedStructure.comparison,
      NatIso.ofComponents.app]
    rfl
  have hc := comparison_unit_formula S S₀ (systemObject l E W) h₀.unitIso
  change (S.monoidal.leftUnitor S.monoidal.tensorUnit).hom ≫
      (tensorSystemUnit l E W).hom =
    S.tensor.map (Prod.mkHom (tensorSystemUnit l E W).hom
      (tensorSystemUnit l E W).hom) ≫
      r.inv ≫ DerivedCategory.Q.map (regularUnitComplex_multiplication l E W).hom
  rw [← hcmp, Category.assoc, hmul]
  rw [he]
  simpa only [Iso.trans_assoc] using hc

end WeilConjectures.CompletedUnitPullback
