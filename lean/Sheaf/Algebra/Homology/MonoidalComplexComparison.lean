/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp

/-! # Monoidal composition comparisons on cochain complexes

Source: the tensor-summand construction of total complexes, Stacks Tags 03EK and 06YP.

(blueprint: lem-pur-u2-monoidal-complex-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Preadditive C] [Preadditive D]
  [Preadditive E] [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ E), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [F.Monoidal] [G.Additive]
  [G.Monoidal] [H.Additive] [H.Monoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) H]
  (e : F ⋙ G ≅ H)


/-- A monoidal comparison of additive functors remains monoidal on total complexes.
The unit equation is its ordinary degree-zero equation, with the single-complex
identifications cancelled. The tensor equation is checked on each total-tensor
summand, using naturality and the ordinary monoidal equation.
Source: literature/stacks-project/sites-cohomology.tex; Tag 06YP; signed direct-sum total tensor;
canonical termwise monoidal comparisons.
(blueprint: lem-pur-u2-monoidal-complex-comparison). -/
theorem mapCochainComplexCompIso_monoidal [NatTrans.IsMonoidal e.hom] :
    let := mapCochainComplexMonoidal F
    let := mapCochainComplexMonoidal G
    let := mapCochainComplexMonoidal H
    NatTrans.IsMonoidal (mapHomologicalComplexCompIso e (.up ℤ)).hom := by
  let := mapCochainComplexMonoidal F
  let := mapCochainComplexMonoidal G
  let := mapCochainComplexMonoidal H
  refine ⟨?_, fun P Q ↦ ?_⟩
  · apply HomologicalComplex.from_single_hom_ext (j := (0 : ℤ))
    change ((G.mapCochainComplexεIso).hom.f 0 ≫
      G.map ((F.mapCochainComplexεIso).hom.f 0)) ≫
      e.hom.app _ = (H.mapCochainComplexεIso).hom.f 0
    rw [mapCochainComplexεIso_hom_f_zero G,
      mapCochainComplexεIso_hom_f_zero F,
      mapCochainComplexεIso_hom_f_zero H]
    let eC := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)
    let eD := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ D)
    let eE := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ E)
    simp only [G.map_comp, Category.assoc]
    rw [← G.map_comp_assoc eD.inv eD.hom, eD.inv_hom_id, G.map_id, Category.id_comp]
    erw [e.hom.naturality eC.inv]
    have hu := NatTrans.IsMonoidal.unit (τ := e.hom)
    change (LaxMonoidal.ε G ≫ G.map (LaxMonoidal.ε F)) ≫
      e.hom.app (𝟙_ C) = LaxMonoidal.ε H at hu
    simp only [Category.assoc] at hu
    rw [← Category.assoc (G.map (LaxMonoidal.ε F)),
      ← Category.assoc (LaxMonoidal.ε G), hu]
  · apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simp only [HomologicalComplex.comp_f]
    change HomologicalComplex.ιTensorObj _ _ p q n h ≫
      ((G.mapCochainComplexμIso ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q)).hom.f n ≫
        G.map ((F.mapCochainComplexμIso P Q).hom.f n)) ≫ e.hom.app _ = _
    simp only [Category.assoc]
    erw [ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
    rw [← G.map_comp_assoc, ιTensorObj_mapCochainComplexμIso_hom_f, G.map_comp]
    simp only [Category.assoc]
    change LaxMonoidal.μ G _ _ ≫ G.map (LaxMonoidal.μ F _ _) ≫
      G.map (F.map (HomologicalComplex.ιTensorObj P Q p q n h)) ≫ e.hom.app _ = _
    erw [e.hom.naturality]
    have ht := NatTrans.IsMonoidal.tensor (τ := e.hom) (P.X p) (Q.X q)
    simp only [LaxMonoidal.comp_μ, Category.assoc] at ht
    erw [reassoc_of% ht]
    erw [CochainComplex.ιTensorObj_tensorHom_f_assoc,
      ιTensorObj_mapCochainComplexμIso_hom_f]
    rfl

end CategoryTheory.Functor
