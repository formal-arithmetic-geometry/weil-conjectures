/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.SmoothPurity.OrdinaryProductTransposeData

import Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose
import Sheaf.SmoothPurity.OrdinaryTripleLeftComparison
import Sheaf.SmoothPurity.OrdinaryTripleRightComparison

/-! # Triple ordinary external-product transposes

Source: blueprint sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md, clauses (i)--(ii)
(blueprint: lem-pur-ordinary-triple-product-transpose).

The fixed-scalar presentation is the ordinary unbounded category of constant-A modules.
A cartesian product diagram chooses a common representative for both triple products;
its projection equations implement their canonical identification by the universal property.
Every comparison below is the published pullback, tensor, or direct-image compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] ordinaryTripleLeft ordinaryTripleRight ordinaryTripleCounit
  ordinaryTripleLeftIdentification ordinaryTripleRightIdentification ordinaryTripleFactor
  ordinaryPushCongr

private theorem transpose_transport {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) {F : P.ordinaryCategory Y} {K : P.ordinaryCategory X}
    (a : F ⟶ (P.ordinaryPush f).obj K) :
    ((P.ordinaryAdj g).homEquiv _ _).symm
        (a ≫ (P.ordinaryPushCongr h).hom.app K) =
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) h.symm).hom.app F ≫
        ((P.ordinaryAdj f).homEquiv _ _).symm a := by
  subst g
  simp [ordinaryPushCongr, leftDerivedUpperStarCongr]

private theorem associate_four {C : Type*} [Category* C]
    {A B C' D E : C} (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ D) (d : D ⟶ E) :
    a ≫ b ≫ c ≫ d = ((a ≫ b) ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem associate_five {C : Type*} [Category* C]
    {A B C' D E F : C} (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ D)
    (d : D ⟶ E) (e : E ⟶ F) :
    a ≫ b ≫ c ≫ d ≫ e = (((a ≫ b) ≫ c) ≫ d) ≫ e := by
  simp only [Category.assoc]

private theorem comparison_naturality
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (μ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    {K K' L L' : C} (x : K ⟶ K') (y : L ⟶ L') :
    F.map (x ⊗ₘ y) ≫ (μ.app K').app L' =
      (μ.app K).app L ≫ (F.map x ⊗ₘ F.map y) := by
  have h₁ : F.map (x ▷ L) ≫ (μ.app K').app L =
      (μ.app K).app L ≫ F.map x ▷ F.obj L :=
    NatTrans.congr_app (μ.naturality x) L
  have h₂ : F.map (K' ◁ y) ≫ (μ.app K').app L' =
      (μ.app K').app L ≫ F.obj K' ◁ F.map y :=
    (μ.app K').naturality y
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
    Functor.map_comp, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

private theorem pull_tensor_naturality
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F F' G G' : DerivedCategory (Sheaf (ProEt.topology Y) A)}
    (x : F ⟶ F') (y : G ⟶ G') :
    (upperStar A f).leftDerivedFunctor.map (x ⊗ₘ y) ≫
        (leftDerivedUpperStarTensorIso A f F' G').hom =
      (leftDerivedUpperStarTensorIso A f F G).hom ≫
        ((upperStar A f).leftDerivedFunctor.map x ⊗ₘ
          (upperStar A f).leftDerivedFunctor.map y) := by
  exact comparison_naturality (upperStar A f).leftDerivedFunctor
    (leftDerivedUpperStarTensorNatIso A f).hom x y

private theorem tensor_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F F' G G' : P.ordinaryCategory Y} (x : F ⟶ F') (y : G ⟶ G') :
    (P.ordinaryPull f).map (x ⊗ₘ y) ≫ (P.ordinaryTensorComparison f F' G').hom =
      (P.ordinaryTensorComparison f F G).hom ≫
        ((P.ordinaryPull f).map x ⊗ₘ (P.ordinaryPull f).map y) := by
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  exact pull_tensor_naturality (ModuleCat.{u + 1} P.Coefficient) f x y

@[reassoc] private theorem binary_naturality {W X Y B : Scheme.{u}}
    {r : W ⟶ X} {t : W ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : IsPullback r t f g)
    {F F' G G' : P.ordinaryCategory B} (x : F ⟶ F') (y : G ⟶ G')
    (K : P.ordinaryCategory X) (L : P.ordinaryCategory Y)
    (k : (P.ordinaryPull f).obj F' ⟶ K) (l : (P.ordinaryPull g).obj G' ⟶ L) :
    (P.ordinaryPull (t ≫ g)).map (x ⊗ₘ y) ≫
        P.ordinaryBinaryEvaluation sq F' G' K L k l =
      P.ordinaryBinaryEvaluation sq F G K L
        ((P.ordinaryPull f).map x ≫ k) ((P.ordinaryPull g).map y ≫ l) := by
  let e := (P.ordinaryTripleFactor r f (t ≫ g) sq.w.symm).hom
  let c := (P.ordinaryPullComposition t g).hom
  have hx : (P.ordinaryPull (t ≫ g)).map x ≫ e.app F' ≫ (P.ordinaryPull r).map k =
      e.app F ≫ (P.ordinaryPull r).map ((P.ordinaryPull f).map x ≫ k) := by
    rw [e.naturality_assoc]
    simp only [Functor.comp_map, Functor.map_comp]
  have hy : (P.ordinaryPull (t ≫ g)).map y ≫ c.app G' ≫ (P.ordinaryPull t).map l =
      c.app G ≫ (P.ordinaryPull t).map ((P.ordinaryPull g).map y ≫ l) := by
    rw [c.naturality_assoc]
    simp only [Functor.comp_map, Functor.map_comp]
  unfold ordinaryBinaryEvaluation
  rw [reassoc_of% (tensor_naturality P (t ≫ g) x y)]
  change _ ≫ (_ ⊗ₘ _) ≫ (e.app F' ⊗ₘ c.app G') ≫ (_ ⊗ₘ _) =
    _ ≫ (e.app F ⊗ₘ c.app G) ≫ (_ ⊗ₘ _)
  simp only [tensorHom_comp_tensorHom, hx, hy]

/-- Both actual iterated ordinary products have precisely the three-counit transpose,
and consequently are equal, on the whole unbounded finite-coefficient categories.
Source: blueprint relative Kunneth coherence proof, clauses (i)--(ii)
(blueprint: lem-pur-ordinary-triple-product-transpose).

Proof:
1. Adjunction naturality transposes source precomposition to pulled-back
   precomposition and direct-image postcomposition to postcomposition. Equality
   transport is reversed by transposition.
2. The binary product transpose calculation identifies each outer product's
   transpose with ordinaryBinaryEvaluation. Naturality of the tensor comparison
   and pullback compositor moves each inner product to its own transpose.
3. Apply the same binary calculation to the inner products. The left and right
   pullback/tensor comparison equations identify the resulting nested evaluations
   with ordinaryTripleEvaluation on the three actual counits, which is exactly
   ordinaryTripleCounit.
4. Injectivity of the adjunction Hom equivalence gives equality of the products.
   Only canonical comparison isomorphisms have been inverted. -/
theorem ordinaryTripleProductTranspose
    (B₀ X₁₀ X₂₀ X₃₀ : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated B₀.hom] [LocallyOfFiniteType B₀.hom] [QuasiCompact B₀.hom]
    [IsSeparated X₁₀.hom] [LocallyOfFiniteType X₁₀.hom] [QuasiCompact X₁₀.hom]
    [IsSeparated X₂₀.hom] [LocallyOfFiniteType X₂₀.hom] [QuasiCompact X₂₀.hom]
    [IsSeparated X₃₀.hom] [LocallyOfFiniteType X₃₀.hom] [QuasiCompact X₃₀.hom]
    (f₁₀ : X₁₀ ⟶ B₀) (f₂₀ : X₂₀ ⟶ B₀) (f₃₀ : X₃₀ ⟶ B₀)
    [IsSeparated f₁₀.left] [LocallyOfFiniteType f₁₀.left] [QuasiCompact f₁₀.left]
    [IsSeparated f₂₀.left] [LocallyOfFiniteType f₂₀.left] [QuasiCompact f₂₀.left]
    [IsSeparated f₃₀.left] [LocallyOfFiniteType f₃₀.left] [QuasiCompact f₃₀.left]
    (d₀ : OrdinaryTripleProductDiagram f₁₀.left f₂₀.left f₃₀.left)
    (K₀ : P.ordinaryCategory X₁₀.left) (L₀ : P.ordinaryCategory X₂₀.left)
    (M₀ : P.ordinaryCategory X₃₀.left) :
    ((P.ordinaryAdj (d₀.a ≫ (d₀.p₂ ≫ f₂₀.left))).homEquiv _ _).symm
        (P.ordinaryTripleLeft d₀ K₀ L₀ M₀) = P.ordinaryTripleCounit d₀ K₀ L₀ M₀ ∧
      ((P.ordinaryAdj (d₀.a ≫ (d₀.p₂ ≫ f₂₀.left))).homEquiv _ _).symm
        (P.ordinaryTripleRight d₀ K₀ L₀ M₀) = P.ordinaryTripleCounit d₀ K₀ L₀ M₀ ∧
      P.ordinaryTripleLeft d₀ K₀ L₀ M₀ = P.ordinaryTripleRight d₀ K₀ L₀ M₀ := by
  let F₁ := (P.ordinaryPush f₁₀.left).obj K₀
  let F₂ := (P.ordinaryPush f₂₀.left).obj L₀
  let F₃ := (P.ordinaryPush f₃₀.left).obj M₀
  let x := (P.ordinaryAdj f₁₀.left).counit.app K₀
  let y := (P.ordinaryAdj f₂₀.left).counit.app L₀
  let z := (P.ordinaryAdj f₃₀.left).counit.app M₀
  have hb₁₂ := P.ordinaryBinaryProductTranspose d₀.square₁₂ K₀ L₀
  rw [Adjunction.homEquiv_counit] at hb₁₂
  have hb₂₃ := transpose_transport P d₀.square₂₃.w.symm
    (P.ordinaryProduct d₀.square₂₃ L₀ M₀)
  rw [ordinaryBinaryProductTranspose, Adjunction.homEquiv_counit] at hb₂₃
  have hl : ((P.ordinaryAdj (d₀.a ≫ (d₀.p₂ ≫ f₂₀.left))).homEquiv _ _).symm
      (P.ordinaryTripleLeft d₀ K₀ L₀ M₀) = P.ordinaryTripleCounit d₀ K₀ L₀ M₀ := by
    unfold ordinaryTripleLeft
    rw [associate_four, transpose_transport]
    rw [Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_left_symm, ordinaryBinaryProductTranspose,
      binary_naturality]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, hb₁₂]
    have hc := P.ordinaryTripleLeftComparison d₀ K₀ L₀ M₀ F₁ F₂ F₃ x y z
    unfold ordinaryTripleEvaluation at hc
    unfold ordinaryTripleCounit
    exact hc
  have hr : ((P.ordinaryAdj (d₀.a ≫ (d₀.p₂ ≫ f₂₀.left))).homEquiv _ _).symm
      (P.ordinaryTripleRight d₀ K₀ L₀ M₀) = P.ordinaryTripleCounit d₀ K₀ L₀ M₀ := by
    unfold ordinaryTripleRight
    rw [associate_five, transpose_transport]
    rw [Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_left_symm, ordinaryBinaryProductTranspose]
    simp only [Functor.map_comp, Category.assoc]
    rw [binary_naturality_assoc]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, hb₂₃]
    have hc := P.ordinaryTripleRightComparison d₀ K₀ L₀ M₀ F₁ F₂ F₃ x y z
    unfold ordinaryTripleEvaluation at hc
    unfold ordinaryTripleCounit
    exact hc
  refine ⟨hl, hr, ?_⟩
  exact ((P.ordinaryAdj (d₀.a ≫ (d₀.p₂ ≫ f₂₀.left))).homEquiv _ _).symm.injective
    (hl.trans hr.symm)

end WeilConjectures.PurityFiniteSetting
