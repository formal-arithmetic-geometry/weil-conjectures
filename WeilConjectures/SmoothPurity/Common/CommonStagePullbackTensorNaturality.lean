/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison

/-! # Naturality of the prescribed common-stage pullback tensor comparison

Source: recorded blueprint coefficient conventions, the common-stage paragraph of
`def-weil-derived-pullback-tensor-hom`; Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open CategoryTheory.StageSystem.PairCategory
namespace WeilConjectures

-- Cache the existing category instances while comparing finite-stage arrows.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

private theorem tensor_map_heq {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ D) {A B A' B' M N M' N' : C}
    (hA : A = M) (hB : B = N) (hA' : A' = M') (hB' : B' = N')
    {a : A ⟶ A'} {b : B ⟶ B'} {f : M ⟶ M'} {g : N ⟶ N'}
    (ha : HEq a f) (hb : HEq b g) :
    HEq (T.map (Prod.mkHom a b)) (T.map (Prod.mkHom f g)) := by
  cases hA; cases hB; cases hA'; cases hB'; cases ha; cases hb
  rfl

private theorem conjugated_naturality {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (U : C × C ⥤ C) (V : D × D ⥤ D)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hn : ∀ {M M' N N' : C} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (U.map (Prod.mkHom a b)) ≫ (μ M' N').hom =
        (μ M N).hom ≫ V.map (Prod.mkHom (F.map a) (F.map b)))
    {M M' N N' A A' : C} {B B' S S' P P' Q Q' : D}
    (a : M ⟶ M') (b : N ⟶ N')
    (t : A ≅ U.obj (M, N)) (t' : A' ≅ U.obj (M', N'))
    (p : B ≅ F.obj A) (p' : B' ≅ F.obj A')
    (m : P ≅ F.obj M) (m' : P' ≅ F.obj M')
    (n : Q ≅ F.obj N) (n' : Q' ≅ F.obj N')
    (s : S ≅ V.obj (P, Q)) (s' : S' ≅ V.obj (P', Q')) :
    (p.hom ≫ F.map (t.hom ≫ U.map (Prod.mkHom a b) ≫ t'.inv) ≫ p'.inv) ≫
        (p'.hom ≫ F.map t'.hom ≫ (μ M' N').hom ≫
          V.map (Prod.mkHom m'.inv n'.inv) ≫ s'.inv) =
      (p.hom ≫ F.map t.hom ≫ (μ M N).hom ≫
          V.map (Prod.mkHom m.inv n.inv) ≫ s.inv) ≫
        (s.hom ≫ V.map (Prod.mkHom (m.hom ≫ F.map a ≫ m'.inv)
          (n.hom ≫ F.map b ≫ n'.inv)) ≫ s'.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← F.map_comp_assoc t'.inv t'.hom, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [← V.map_comp_assoc]
  simp only [prod_comp, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn a b]
  rw [← V.map_comp_assoc]
  rfl

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  commonStageTensorComparison commonStagePullbackComparison

end WeilConjectures
