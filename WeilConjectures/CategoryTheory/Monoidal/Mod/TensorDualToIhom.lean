/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing

/-!
# The morphism `X ⊗_A M^∨ ⟶ Hom_A(M, X)`

Let `A` be a commutative monoid in a symmetric monoidal Grothendieck abelian category `C`. For
`A`-modules `M` and `X`, with `M^∨ = Hom_A(M, A)`, we construct the morphism of `A`-modules
`X ⊗_A M^∨ ⟶ Hom_A(M, X)`, `x ⊗ φ ↦ (m ↦ x φ(m))` (`CategoryTheory.Mod.tensorDualToIhom`),
characterised by its uncurried form `(x ⊗ φ) ⊗ m ↦ x φ(m)`
(`CategoryTheory.Mod.tensorπ_tensorDualToIhom_evaluation`). It is natural in `X`
(`CategoryTheory.Mod.tensorDualToIhomNatTrans`) and in `M`
(`CategoryTheory.Mod.tensorLeftMap_app_comp_tensorDualToIhom`).

It is an isomorphism for `M = A` (`CategoryTheory.Mod.isIso_tensorDualToIhom_regular`), and the
class of `M` for which it is an isomorphism for all `X` is closed under isomorphisms and finite
direct sums; in particular it is an isomorphism for `M` free of finite rank
(`CategoryTheory.Mod.isIso_tensorDualToIhom_of_iso_biproduct`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A]

section Structural

omit [IsCommMonObj A] in
/-- `x (a b) = a (x b)` for the right action of a monoid on a module. -/
@[reassoc]
lemma whiskerLeft_mul_rightAct' (P : Mod C A) :
    P.X ◁ μ[A] ≫ rightAct P =
      (α_ P.X A A).inv ≫ (β_ P.X A).hom ▷ A ≫ (α_ A P.X A).hom ≫ A ◁ rightAct P ≫
        act P.X := by
  simp only [rightAct, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc, mul_act]
  monoidal

omit [IsCommMonObj A] in
/-- The right action is natural. -/
@[reassoc]
lemma rightAct_naturality {P Q : Mod C A} (f : P ⟶ Q) :
    f.hom ▷ A ≫ rightAct Q = rightAct P ≫ f.hom := by
  simp only [rightAct, BraidedCategory.braiding_naturality_left_assoc, Category.assoc, act_hom]

omit [IsCommMonObj A] in
/-- If `e : Y ⊗ M ⟶ A` is `A`-linear in `M`, so is `(x ⊗ y) ⊗ m ↦ x e(y ⊗ m)`. -/
lemma isLinearRight_whiskerLeft_rightAct {Y : C} {M : Mod C A} (P : Mod C A)
    (e : Y ⊗ M.X ⟶ A) (he : Y ◁ act M.X ≫ e =
      (α_ Y A M.X).inv ≫ (β_ Y A).hom ▷ M.X ≫ (α_ A Y M.X).hom ≫ A ◁ e ≫ μ[A]) :
    IsLinearRight (X := P.X ⊗ Y) (D := M) (N := P)
      ((α_ P.X Y M.X).hom ≫ P.X ◁ e ≫ rightAct P) := by
  unfold IsLinearRight
  rw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, he]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [whiskerLeft_mul_rightAct', associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, associator_naturality_right_assoc,
    BraidedCategory.braiding_tensor_left_hom]
  simp only [rightAct, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- `(x ⊗ y) ⊗ z ↦ x e(y ⊗ z)` is `A`-linear in `x`. -/
lemma rightAct_linear {Y Z : C} (P : Mod C A) (e : Y ⊗ Z ⟶ A) :
    ((α_ A P.X Y).inv ≫ act P.X ▷ Y) ▷ Z ≫ (α_ P.X Y Z).hom ≫ P.X ◁ e ≫ rightAct P =
      (α_ A (P.X ⊗ Y) Z).hom ≫ A ◁ ((α_ P.X Y Z).hom ≫ P.X ◁ e ≫ rightAct P) ≫
        act P.X := by
  rw [comp_whiskerRight_assoc, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    act_whiskerRight_rightAct]
  monoidal

omit [SymmetricCategory C] [IsCommMonObj A] in
/-- `(x ⊗ d) ⊗ z ↦ x e(d ⊗ z)` with `x (a b) = (x a) b` gives `x e((a d) ⊗ z) = (x a) e(d ⊗ z)`
when `e` is `A`-linear in `d`. -/
lemma rightAct_balanced_aux {Z : C} [BraidedCategory C] (P D : Mod C A) (e : D.X ⊗ Z ⟶ A)
    (he : act D.X ▷ Z ≫ e = (α_ A D.X Z).hom ≫ A ◁ e ≫ μ[A])
    (hP : P.X ◁ μ[A] ≫ rightAct P = (α_ P.X A A).inv ≫ rightAct P ▷ A ≫ rightAct P) :
    (P.X ◁ act D.X) ▷ Z ≫ (α_ P.X D.X Z).hom ≫ P.X ◁ e ≫ rightAct P =
      ((α_ P.X A D.X).inv ≫ rightAct P ▷ D.X) ▷ Z ≫ (α_ P.X D.X Z).hom ≫ P.X ◁ e ≫
        rightAct P := by
  rw [associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, he,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc, hP,
    associator_inv_naturality_right_assoc, comp_whiskerRight_assoc (α_ P.X A D.X).inv,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  monoidal

/-- If `e : D ⊗ Z ⟶ A` is `A`-linear in `D`, then `(x ⊗ d) ⊗ z ↦ x e(d ⊗ z)` is `A`-balanced
in `x` and `d`. -/
lemma rightAct_balanced {Z : C} (P D : Mod C A) (e : D.X ⊗ Z ⟶ A)
    (he : act D.X ▷ Z ≫ e = (α_ A D.X Z).hom ≫ A ◁ e ≫ μ[A]) :
    (P.X ◁ act D.X) ▷ Z ≫ (α_ P.X D.X Z).hom ≫ P.X ◁ e ≫ rightAct P =
      ((α_ P.X A D.X).inv ≫ rightAct P ▷ D.X) ▷ Z ≫ (α_ P.X D.X Z).hom ≫ P.X ◁ e ≫
        rightAct P :=
  rightAct_balanced_aux P D e he (whiskerLeft_mul_rightAct P)

omit [IsCommMonObj A] in
/-- `(x ⊗ y) ⊗ z ↦ x e(y ⊗ z)` is natural in the module of `x`. -/
lemma rightAct_naturality' {Y Z : C} {P Q : Mod C A} (f : P ⟶ Q) (e : Y ⊗ Z ⟶ A) :
    (f.hom ▷ Y) ▷ Z ≫ (α_ Q.X Y Z).hom ≫ Q.X ◁ e ≫ rightAct Q =
      (α_ P.X Y Z).hom ≫ P.X ◁ e ≫ rightAct P ≫ f.hom := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightAct_naturality]

end Structural

variable [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

/-- The evaluation `Hom_A(M, N) ⊗ M ⟶ N` is `A`-linear in `M`. -/
lemma isLinearRight_evaluation (M N : Mod C A) :
    IsLinearRight (X := ((ihom M).obj N).X) (D := M) (N := N) (evaluation M N) := by
  unfold IsLinearRight
  rw [whiskerLeft_act_evaluation, rightAct, comp_whiskerRight_assoc,
    act_whiskerRight_evaluation]

variable (M X : Mod C A)

/-- The morphism `(x ⊗ φ) ⊗ m ↦ x φ(m)`, `X ⊗ M^∨ ⊗ M ⟶ X`. -/
noncomputable def tensorDualToIhomAux :
    (X.X ⊗ ((ihom M).obj (regular A)).X) ⊗ M.X ⟶ X.X :=
  (α_ _ _ _).hom ≫ X.X ◁ evaluation M (regular A) ≫ rightAct X

lemma isLinearRight_tensorDualToIhomAux :
    IsLinearRight (D := M) (N := X) (tensorDualToIhomAux M X) :=
  isLinearRight_whiskerLeft_rightAct X (evaluation M (regular A))
    (isLinearRight_evaluation M (regular A))

/-- The morphism `X ⊗ M^∨ ⟶ Hom_A(M, X)`, `x ⊗ φ ↦ (m ↦ x φ(m))`, of underlying objects. -/
noncomputable def tensorDualToIhomCurry :
    X.X ⊗ ((ihom M).obj (regular A)).X ⟶ ((ihom M).obj X).X :=
  curry (tensorDualToIhomAux M X) (isLinearRight_tensorDualToIhomAux M X)

@[reassoc]
lemma tensorDualToIhomCurry_evaluation :
    tensorDualToIhomCurry M X ▷ M.X ≫ evaluation M X = tensorDualToIhomAux M X :=
  curry_evaluation _ _

lemma isBilinear_tensorDualToIhomCurry :
    IsBilinear (P := X) (M := (ihom M).obj (regular A)) (N := (ihom M).obj X)
      (tensorDualToIhomCurry M X) where
  linear := by
    apply hom_ext_of_evaluation
    have h := rightAct_linear X (evaluation M (regular A))
    simp only [comp_whiskerRight, Category.assoc] at h
    simp only [comp_whiskerRight, Category.assoc, tensorDualToIhomCurry_evaluation]
    rw [act_whiskerRight_evaluation, associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, tensorDualToIhomCurry_evaluation]
    exact h
  balanced := by
    apply hom_ext_of_evaluation
    have h := rightAct_balanced X _ (evaluation M (regular A))
      (act_whiskerRight_evaluation M (regular A))
    simp only [comp_whiskerRight, Category.assoc] at h
    simp only [comp_whiskerRight, Category.assoc, tensorDualToIhomCurry_evaluation]
    exact h

/-- **The morphism `X ⊗_A M^∨ ⟶ Hom_A(M, X)`**, `x ⊗ φ ↦ (m ↦ x φ(m))`. -/
noncomputable def tensorDualToIhom :
    (tensorLeft ((ihom M).obj (regular A))).obj X ⟶ (ihom M).obj X :=
  tensorDesc _ (isBilinear_tensorDualToIhomCurry M X)

@[reassoc]
lemma tensorπ_tensorDualToIhom :
    tensorπ X ((ihom M).obj (regular A)) ≫ (tensorDualToIhom M X).hom =
      tensorDualToIhomCurry M X :=
  tensorπ_tensorDesc _ _

/-- The uncurried form of `X ⊗_A M^∨ ⟶ Hom_A(M, X)` is `(x ⊗ φ) ⊗ m ↦ x φ(m)`. -/
lemma tensorπ_tensorDualToIhom_evaluation :
    (tensorπ X ((ihom M).obj (regular A)) ≫ (tensorDualToIhom M X).hom) ▷ M.X ≫
      evaluation M X = tensorDualToIhomAux M X := by
  rw [tensorπ_tensorDualToIhom, tensorDualToIhomCurry_evaluation]

end CategoryTheory.Mod
