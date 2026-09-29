/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Complements on the tensor product of cochain complexes

For cochain complexes indexed by `ℤ`, we describe the differential of the tensor product
`P ⊗ K` and the morphism `P ◁ f` on the summands `P.X p ⊗ K.X q`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (P K : CochainComplex C ℤ)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
@[reassoc]
lemma ιTensorObj_d (p q r r' : ℤ) (h : p + q = r) (h' : r + 1 = r') :
    HomologicalComplex.ιTensorObj P K p q r h ≫ (P ⊗ K).d r r' =
      P.d p (p + 1) ▷ K.X q ≫ HomologicalComplex.ιTensorObj P K (p + 1) q r' (by lia) +
        p.negOnePow • (P.X p ◁ K.d q (q + 1) ≫
          HomologicalComplex.ιTensorObj P K p (q + 1) r' (by lia)) := by
  rw [show (P ⊗ K).d r r' = (HomologicalComplex.tensorObj P K).d r r' from rfl,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
      (by simp; lia),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
      (by simp; lia)]
  simp

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
variable {K} in
@[reassoc]
lemma ιTensorObj_whiskerLeft_f {K' : CochainComplex C ℤ} (f : K ⟶ K') (p q r : ℤ)
    (h : p + q = r) :
    HomologicalComplex.ιTensorObj P K p q r h ≫ (P ◁ f).f r =
      P.X p ◁ f.f q ≫ HomologicalComplex.ιTensorObj P K' p q r h := by
  rw [show (P ◁ f).f r = (HomologicalComplex.tensorHom (𝟙 P) f).f r from rfl]
  simp

end CochainComplex
