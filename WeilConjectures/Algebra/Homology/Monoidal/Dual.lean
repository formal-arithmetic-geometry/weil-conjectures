/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C]

section

variable {X Y : C} [HasRightDual X] [HasRightDual Y]

omit [HasZeroObject C] in
lemma rightAdjointMate_zero' : (0 : X ⟶ Y)ᘁ = 0 := by
  simp [rightAdjointMate]

end

lemma units_smul_smul_add_self {M : Type*} [AddCommGroup M] (u v : ℤˣ) (x : M)
    (h : u * v = -1) : u • v • x + x = 0 := by
  rw [smul_smul, h, Units.neg_smul, one_smul, neg_add_cancel]

omit [HasZeroObject C] in
lemma units_smul_whiskerRight {X Y : C} (u : ℤˣ) (f : X ⟶ Y) (Z : C) :
    (u • f) ▷ Z = u • (f ▷ Z) := by
  rw [Units.smul_def, Units.smul_def]
  exact Functor.map_zsmul (tensorRight Z)

omit [HasZeroObject C] in
lemma whiskerLeft_units_smul (X : C) {Y Z : C} (u : ℤˣ) (f : Y ⟶ Z) :
    X ◁ (u • f) = u • (X ◁ f) := by
  rw [Units.smul_def, Units.smul_def]
  exact Functor.map_zsmul (tensorLeft X)

variable (K : CochainComplex C ℤ) [∀ n, HasRightDual (K.X n)]

/-- The termwise right dual of a cochain complex. -/
noncomputable def rightDual : CochainComplex C ℤ where
  X n := (K.X (-n))ᘁ
  d i j := j.negOnePow • (K.d (-j) (-i))ᘁ
  shape i j h := by
    rw [K.shape (-j) (-i) (by simp at h ⊢; omega), rightAdjointMate_zero', smul_zero]
  d_comp_d' i j k _ _ := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, ← comp_rightAdjointMate, K.d_comp_d,
      rightAdjointMate_zero', smul_zero, smul_zero]

lemma rightDual_X (n : ℤ) : K.rightDual.X n = (K.X (-n))ᘁ := rfl

lemma rightDual_d (i j : ℤ) : K.rightDual.d i j = j.negOnePow • (K.d (-j) (-i))ᘁ := rfl

variable [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

namespace rightDual

/-- The evaluation `K^∨.X q ⊗ K.X p ⟶ 𝟙_ C` on a summand of degree `q + p = 0`. -/
noncomputable def evalPQ (q p : ℤ) (h : q + p = 0) : K.rightDual.X q ⊗ K.X p ⟶ 𝟙_ C :=
  K.rightDual.X q ◁ (K.XIsoOfEq (show p = -q by omega)).hom ≫ ε_ (K.X (-q)) (K.X (-q))ᘁ

lemma evalPQ_comm (q p : ℤ) (h : q + p + 1 = 0) :
    K.rightDual.d q (q + 1) ▷ K.X p ≫ evalPQ K (q + 1) p (by omega) +
      q.negOnePow • (K.rightDual.X q ◁ K.d p (p + 1) ≫ evalPQ K q (p + 1) (by omega)) = 0 := by
  obtain rfl : q = -p - 1 := by omega
  have hd : (K.XIsoOfEq (show p = -(-p - 1 + 1) by omega)).hom ≫ K.d (-(-p - 1 + 1)) (-(-p - 1)) =
      K.d p (p + 1) ≫ (K.XIsoOfEq (show p + 1 = -(-p - 1) by omega)).hom := by
    rw [HomologicalComplex.XIsoOfEq_hom_comp_d, HomologicalComplex.d_comp_XIsoOfEq_hom]
  have hs : (-p - 1 + 1).negOnePow = -(-p - 1).negOnePow := by
    rw [Int.negOnePow_succ]
  simp only [evalPQ, rightDual, hs]
  rw [units_smul_whiskerRight, Linear.units_smul_comp, ← whisker_exchange_assoc,
    rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc, hd, whiskerLeft_comp_assoc,
    Units.neg_smul]
  exact neg_add_cancel _

/-- The evaluation `K^∨ ⊗ K ⟶ 𝟙_` of the termwise dual. -/
noncomputable def eval : K.rightDual ⊗ K ⟶ 𝟙_ (CochainComplex C ℤ) :=
  HomologicalComplex.mkHomToSingle
    (HomologicalComplex.mapBifunctorDesc (fun q p h ↦ evalPQ K q p h)) (by
      intro i hi
      have hi' : i + 1 = 0 := hi
      refine HomologicalComplex.mapBifunctor.hom_ext (fun q p h ↦ ?_)
      have h' : q + p = i := h
      rw [comp_zero, ← assoc]
      erw [ιTensorObj_d _ _ q p i 0 h' hi']
      rw [Preadditive.add_comp, assoc, Linear.units_smul_comp, assoc]
      erw [HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
      exact evalPQ_comm K q p (by omega))

/-- The coevaluation `𝟙_ C ⟶ K.X p ⊗ K^∨.X q` on a summand of degree `p + q = 0`. -/
noncomputable def coevPQ (p q : ℤ) (h : p + q = 0) : 𝟙_ C ⟶ K.X p ⊗ K.rightDual.X q :=
  η_ (K.X (-q)) (K.X (-q))ᘁ ≫ (K.XIsoOfEq (show -q = p by omega)).hom ▷ (K.X (-q))ᘁ

lemma coevPQ_eq_zero (p q : ℤ) (h : p + q = 0) (hp : IsZero (K.X p)) : coevPQ K p q h = 0 :=
  (((curriedTensor C).map_isZero hp).obj _).eq_of_tgt _ _

/-- The differential of `K ⊗ K^∨` applied to `coevPQ`, first part. -/
noncomputable def coevD₁ (p q p₁ : ℤ) (h : p + q = 0) (hp : p + 1 = p₁) :
    𝟙_ C ⟶ (K ⊗ K.rightDual).X 1 :=
  coevPQ K p q h ≫ K.d p p₁ ▷ K.rightDual.X q ≫
    HomologicalComplex.ιTensorObj K K.rightDual p₁ q 1 (by omega)

/-- The differential of `K ⊗ K^∨` applied to `coevPQ`, second part. -/
noncomputable def coevD₂ (p q q₁ : ℤ) (h : p + q = 0) (hq : q + 1 = q₁) :
    𝟙_ C ⟶ (K ⊗ K.rightDual).X 1 :=
  p.negOnePow • (coevPQ K p q h ≫ K.X p ◁ K.rightDual.d q q₁ ≫
    HomologicalComplex.ιTensorObj K K.rightDual p q₁ 1 (by omega))

lemma coevD₁_congr (p q p₁ p' q' p₁' : ℤ) (h : p + q = 0) (hp : p + 1 = p₁)
    (h' : p' + q' = 0) (hp' : p' + 1 = p₁') (e : p = p') (e' : q = q') :
    coevD₁ K p q p₁ h hp = coevD₁ K p' q' p₁' h' hp' := by
  subst e e' hp hp'
  rfl

lemma coevD₂_add_coevD₁ (p q q₁ p' : ℤ) (h : p + q = 0) (hq : q + 1 = q₁)
    (hp' : p' + 1 = p) :
    coevD₂ K p q q₁ h hq + coevD₁ K p' q₁ p (by omega) hp' = 0 := by
  subst hq hp'
  obtain rfl : q = -p' - 1 := by omega
  have hd : K.d (-(-p' - 1 + 1)) (-(-p' - 1)) ≫
      (K.XIsoOfEq (show -(-p' - 1) = p' + 1 by omega)).hom =
      (K.XIsoOfEq (show -(-p' - 1 + 1) = p' by omega)).hom ≫ K.d p' (p' + 1) := by
    rw [HomologicalComplex.d_comp_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_hom_comp_d]
  have hs : (p' + 1).negOnePow * (-p' - 1 + 1).negOnePow = -1 := by
    rw [← Int.negOnePow_add, show p' + 1 + (-p' - 1 + 1) = 1 by omega, Int.negOnePow_one]
  simp only [coevD₂, coevD₁, coevPQ, rightDual, whiskerLeft_units_smul, Linear.units_smul_comp,
    Linear.comp_units_smul, assoc]
  rw [← whisker_exchange_assoc, coevaluation_comp_rightAdjointMate_assoc,
    ← comp_whiskerRight_assoc, hd, comp_whiskerRight_assoc]
  exact units_smul_smul_add_self _ _ _ hs

end rightDual

end CochainComplex
