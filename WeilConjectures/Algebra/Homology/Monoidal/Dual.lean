/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Data.Int.Interval
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

variable (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

/-- The degree `0` component `𝟙_ C ⟶ (K ⊗ K^∨).X 0` of the coevaluation. -/
noncomputable def coevZero : 𝟙_ C ⟶ (K ⊗ K.rightDual).X 0 :=
  ∑ p ∈ Finset.Icc a b,
    coevPQ K p (-p) (by simp) ≫ HomologicalComplex.ιTensorObj K K.rightDual p (-p) 0 (by simp)

lemma isZero_X_of_notMem (p : ℤ) (hp : p ∉ Finset.Icc a b) : IsZero (K.X p) := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hp
  rcases hp with hp | hp
  · exact K.isZero_of_isStrictlyGE a p hp
  · exact K.isZero_of_isStrictlyLE b p hp

lemma coevZero_comp_d : coevZero K a b ≫ (K ⊗ K.rightDual).d 0 1 = 0 := by
  let f : ℤ → (𝟙_ C ⟶ (K ⊗ K.rightDual).X 1) := fun p ↦ coevD₁ K p (-p) (p + 1) (by simp) rfl
  have hf : ∀ p ∉ Finset.Icc a b, f p = 0 := fun p hp ↦ by
    simp only [f, coevD₁, coevPQ_eq_zero K p (-p) (by simp) (isZero_X_of_notMem K a b p hp),
      zero_comp]
  have hf' : ∀ p ∉ Finset.Icc a b, f (p - 1) = 0 := fun p hp ↦ by
    by_cases hp' : p - 1 ∈ Finset.Icc a b
    · obtain rfl : p = b + 1 := by simp only [Finset.mem_Icc] at hp hp'; omega
      simp only [f, coevD₁]
      rw [(K.isZero_of_isStrictlyLE b (b + 1 - 1 + 1) (by omega)).eq_of_tgt (K.d _ _) 0]
      simp
    · exact hf _ hp'
  have e : ∀ p : ℤ, coevPQ K p (-p) (by simp) ≫
      HomologicalComplex.ιTensorObj K K.rightDual p (-p) 0 (by simp) ≫
        (K ⊗ K.rightDual).d 0 1 = f p - f (p - 1) := fun p ↦ by
    erw [ιTensorObj_d K K.rightDual p (-p) 0 1 (by simp) rfl]
    have h := coevD₂_add_coevD₁ K p (-p) (-p + 1) (p - 1) (by simp) rfl (by omega)
    rw [coevD₁_congr K (p - 1) (-p + 1) p (p - 1) (-(p - 1)) (p - 1 + 1) (by omega) (by omega)
      (by simp) rfl rfl (by omega)] at h
    rw [sub_eq_add_neg, ← eq_neg_of_add_eq_zero_left h, Preadditive.comp_add,
      Linear.comp_units_smul]
    rfl
  simp only [coevZero, Preadditive.sum_comp, assoc, e, Finset.sum_sub_distrib]
  rw [← finsum_eq_sum_of_support_subset f (s := Finset.Icc a b) ?_,
    ← finsum_eq_sum_of_support_subset (fun p ↦ f (p - 1)) (s := Finset.Icc a b) ?_]
  · show _ - ∑ᶠ p, f (Equiv.subRight 1 p) = 0
    rw [finsum_comp_equiv (Equiv.subRight 1) (f := f), sub_self]
  · intro p hp
    by_contra hp'
    exact hp (hf' p hp')
  · intro p hp
    by_contra hp'
    exact hp (hf p hp')


/-- The coevaluation `𝟙_ ⟶ K ⊗ K^∨` of the termwise dual of a bounded complex. -/
noncomputable def coev : 𝟙_ (CochainComplex C ℤ) ⟶ K ⊗ K.rightDual :=
  HomologicalComplex.mkHomFromSingle (coevZero K a b) (by
    rintro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    exact coevZero_comp_d K a b)

end rightDual

section Unitors

variable (L : CochainComplex C ℤ)

lemma leftUnitor_inv_f (n : ℤ) :
    (λ_ L).inv.f n = (λ_ (L.X n)).inv ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ▷ L.X n ≫
        HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex C ℤ)) L 0 n n (zero_add n) :=
  HomologicalComplex.leftUnitor'_inv L n

lemma rightUnitor_inv_f (n : ℤ) :
    (ρ_ L).inv.f n = (ρ_ (L.X n)).inv ≫
      L.X n ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫
        HomologicalComplex.ιTensorObj L (𝟙_ (CochainComplex C ℤ)) n 0 n (add_zero n) :=
  HomologicalComplex.rightUnitor'_inv L n

end Unitors

end CochainComplex
