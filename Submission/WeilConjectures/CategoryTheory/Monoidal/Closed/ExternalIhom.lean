/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The external internal-hom map

Let `F₁ : D₁ ⥤ C` and `F₂ : D₂ ⥤ C` be lax monoidal functors into a braided monoidal closed
category. The *external internal-hom map*
(`CategoryTheory.MonoidalClosed.externalIhomMap`)

`F₁(E₁ ⟶ L₁) ⊗ F₂(E₂ ⟶ L₂) ⟶ (F₁ E₁ ⊗ F₂ E₂ ⟶ F₁ L₁ ⊗ F₂ L₂)`

is the transpose of the two evaluations, through the middle-four interchange `tensorμ`. For
external products of étale sheaves it is the map `β` of `def-sf-kv-maps` (iii).

This file proves the formal properties of this map used to show that `β` is an isomorphism:

* it is unchanged, up to the braidings, when the two factors are exchanged, for a symmetric `C`
  (`CategoryTheory.MonoidalClosed.externalIhomMap_swap`);
* for an adjunction `L ⊣ R` with an invertible projection formula
  `π : L M ⊗ N ≅ L (M ⊗ F N)` (a compactly supported direct image `g_!` and the exceptional
  inverse image `g^!`), the comparison `R (X ⟶ Y) ⟶ (F X ⟶ R Y)`
  (`CategoryTheory.Adjunction.projectionIhomMap`) is an isomorphism
  (`CategoryTheory.Adjunction.isIso_projectionIhomMap`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

namespace MonoidalClosed

section External

universe v₀ v₁ v₂ u₀ u₁ u₂

variable {C : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₀} C] [Category.{v₁} D₁]
  [Category.{v₂} D₂] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [MonoidalCategory D₁] [MonoidalClosed D₁] [MonoidalCategory D₂] [MonoidalClosed D₂]
  (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.LaxMonoidal] [F₂.LaxMonoidal]

/-- The external internal-hom map
`F₁(E₁ ⟶[D₁] L₁) ⊗ F₂(E₂ ⟶[D₂] L₂) ⟶ (F₁ E₁ ⊗ F₂ E₂ ⟶[C] F₁ L₁ ⊗ F₂ L₂)`: the transpose of
`(F₁ E₁ ⊗ F₂ E₂) ⊗ (F₁ H₁ ⊗ F₂ H₂) ⟶ (F₁ E₁ ⊗ F₁ H₁) ⊗ (F₂ E₂ ⊗ F₂ H₂) ⟶ F₁ L₁ ⊗ F₂ L₂`, the
middle-four interchange `tensorμ` followed by the images of the two evaluations
(`Hᵢ = Eᵢ ⟶ Lᵢ`). -/
noncomputable def externalIhomMap (E₁ L₁ : D₁) (E₂ L₂ : D₂) :
    F₁.obj ((ihom E₁).obj L₁) ⊗ F₂.obj ((ihom E₂).obj L₂) ⟶
      (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).obj (F₁.obj L₁ ⊗ F₂.obj L₂) :=
  curry (tensorμ _ _ _ _ ≫
    ((Functor.LaxMonoidal.μ F₁ _ _ ≫ F₁.map ((ihom.ev E₁).app L₁)) ⊗ₘ
      (Functor.LaxMonoidal.μ F₂ _ _ ≫ F₂.map ((ihom.ev E₂).app L₂))))

lemma uncurry_externalIhomMap (E₁ L₁ : D₁) (E₂ L₂ : D₂) :
    uncurry (externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂) = tensorμ _ _ _ _ ≫
      ((μ F₁ _ _ ≫ F₁.map ((ihom.ev E₁).app L₁)) ⊗ₘ (μ F₂ _ _ ≫ F₂.map ((ihom.ev E₂).app L₂))) :=
  uncurry_curry _

end External

section Swap

variable {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [MonoidalCategory D₁] [MonoidalClosed D₁]
  [MonoidalCategory D₂] [MonoidalClosed D₂] (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.LaxMonoidal]
  [F₂.LaxMonoidal]


end Swap

section BaseCase

/-- The transpose of `(ihomObjIsoTensor D X L).inv : D ⊗ L ⟶ (X ⟶ L)` is the transposed
evaluation `X ⊗ (D ⊗ L) ≅ (X ⊗ D) ⊗ L ⟶ L`. -/
lemma uncurry_ihomObjIsoTensor_inv {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] (D X L : C) [ExactPairing D X] :
    uncurry (ihomObjIsoTensor D X L).inv = (α_ _ _ _).inv ≫ ε_ D X ▷ L ≫ (λ_ L).hom := by
  have h₁ := (tensorLeftAdjunction D X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) L
  rw [tensorLeftAdjunction_counit_app] at h₁
  rw [uncurry_eq, ihomObjIsoTensor, ihomIsoTensorLeft, Iso.app_inv,
    Adjunction.rightAdjointUniq_inv_app, ← h₁]
  rfl

/-- **A criterion for maps into an internal hom out of an object with a left dual.** If `D` is
a left dual of `X`, a map `f : H ⟶ (X ⟶ L)` whose transpose is
`X ⊗ H ⟶ X ⊗ (D ⊗ L) ≅ (X ⊗ D) ⊗ L ⟶ L` for an isomorphism `g : H ⟶ D ⊗ L` is an isomorphism. -/
theorem isIso_of_uncurry_eq {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
    {D X L H : C} [ExactPairing D X] (g : H ⟶ D ⊗ L) [IsIso g] (f : H ⟶ (ihom X).obj L)
    (h : uncurry f = X ◁ g ≫ (α_ _ _ _).inv ≫ ε_ D X ▷ L ≫ (λ_ L).hom) : IsIso f := by
  have hf : f = g ≫ (ihomObjIsoTensor D X L).inv := by
    apply uncurry_injective
    rw [h, uncurry_natural_left, uncurry_ihomObjIsoTensor_inv]
  rw [hf]
  infer_instance

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : D ⥤ C) [F.Monoidal]

/-- For a monoidal functor `F` and a left dual `D'` of `E`, the image of the transposed evaluation
`E ⊗ (D' ⊗ L) ≅ (E ⊗ D') ⊗ L ⟶ L` is the transposed evaluation of the image pairing
(`CategoryTheory.ExactPairing.map`). -/
lemma _root_.CategoryTheory.Functor.whiskerLeft_μ_comp_μ_comp_map_evaluation (D' E L : D)
    [ExactPairing D' E] :
    F.obj E ◁ μ F D' L ≫ μ F E (D' ⊗ L) ≫
        F.map ((α_ E D' L).inv ≫ ε_ D' E ▷ L ≫ (λ_ L).hom) =
      (α_ _ _ _).inv ≫ (μ F E D' ≫ F.map (ε_ D' E) ≫ η F) ▷ F.obj L ≫ (λ_ _).hom := by
  rw [F.map_comp, F.map_comp, Functor.LaxMonoidal.associativity_inv_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.map_leftUnitor,
    Functor.Monoidal.μ_δ_assoc, comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]

variable [MonoidalClosed C]

/-- **Monoidal functors preserve internal homs out of objects with a left dual.** For a left
dual `D'` of `E` and a monoidal functor `F`, the transpose
`F (D' ⊗ L) ⟶ (F E ⟶ F L)` of the image of the transposed evaluation is an isomorphism. -/
theorem isIso_curry_μ_comp_map_evaluation (D' E L : D) [ExactPairing D' E] :
    IsIso (curry (μ F E (D' ⊗ L) ≫ F.map ((α_ E D' L).inv ≫ ε_ D' E ▷ L ≫ (λ_ L).hom))) := by
  let := ExactPairing.map F D' E
  refine isIso_of_uncurry_eq (δ F D' L) _ ?_
  rw [uncurry_curry, ← cancel_epi (F.obj E ◁ μ F D' L), ← whiskerLeft_comp_assoc,
    Functor.Monoidal.μ_δ, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  exact F.whiskerLeft_μ_comp_μ_comp_map_evaluation D' E L

/-- The exact pairing of `(X₁, X₂)` and `(Y₁, Y₂)` in a product of monoidal categories induced
by exact pairings of `X₁, Y₁` and of `X₂, Y₂`. -/
@[instance_reducible]
def _root_.CategoryTheory.ExactPairing.prod {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂] (X₁ Y₁ : C₁) (X₂ Y₂ : C₂) [ExactPairing X₁ Y₁]
    [ExactPairing X₂ Y₂] : ExactPairing ((X₁, X₂) : C₁ × C₂) (Y₁, Y₂) where
  coevaluation' := (η_ X₁ Y₁, η_ X₂ Y₂)
  evaluation' := (ε_ X₁ Y₁, ε_ X₂ Y₂)
  coevaluation_evaluation' := Prod.ext (ExactPairing.coevaluation_evaluation X₁ Y₁)
    (ExactPairing.coevaluation_evaluation X₂ Y₂)
  evaluation_coevaluation' := Prod.ext (ExactPairing.evaluation_coevaluation X₁ Y₁)
    (ExactPairing.evaluation_coevaluation X₂ Y₂)

variable [BraidedCategory C]

/-- **The external internal hom of two objects with left duals.** If `P₁, P₂` are left duals of
`A₁, A₂` in a braided monoidal closed category, the transpose of
`(A₁ ⊗ A₂) ⊗ ((P₁ ⊗ Q₁) ⊗ (P₂ ⊗ Q₂)) ⟶ (A₁ ⊗ (P₁ ⊗ Q₁)) ⊗ (A₂ ⊗ (P₂ ⊗ Q₂)) ⟶ Q₁ ⊗ Q₂`, the
middle-four interchange followed by the two transposed evaluations, is an isomorphism: it is the
case of the tensor product functor `C × C ⥤ C` in `isIso_curry_μ_comp_map_evaluation`. -/
theorem isIso_curry_tensorμ_comp_evaluation (P₁ A₁ Q₁ P₂ A₂ Q₂ : C) [ExactPairing P₁ A₁]
    [ExactPairing P₂ A₂] :
    IsIso (curry (tensorμ A₁ A₂ (P₁ ⊗ Q₁) (P₂ ⊗ Q₂) ≫
      (((α_ A₁ P₁ Q₁).inv ≫ ε_ P₁ A₁ ▷ Q₁ ≫ (λ_ Q₁).hom) ⊗ₘ
        ((α_ A₂ P₂ Q₂).inv ≫ ε_ P₂ A₂ ▷ Q₂ ≫ (λ_ Q₂).hom)))) := by
  let := ExactPairing.prod P₁ A₁ P₂ A₂
  exact isIso_curry_μ_comp_map_evaluation (tensor C) (P₁, P₂) (A₁, A₂) (Q₁, Q₂)

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] [MonoidalCategory D₁] [MonoidalClosed D₁]
  [MonoidalCategory D₂] [MonoidalClosed D₂] (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.Monoidal]
  [F₂.Monoidal]

/-- **The external internal-hom map of objects with left duals is an isomorphism.** If `E₁` and
`E₂` have left duals, then for monoidal functors `F₁`, `F₂` into a braided monoidal closed
category the external internal-hom map `F₁(E₁ ⟶ L₁) ⊗ F₂(E₂ ⟶ L₂) ⟶ (F₁ E₁ ⊗ F₂ E₂ ⟶ F₁ L₁ ⊗ F₂ L₂)`
is an isomorphism. -/
theorem isIso_externalIhomMap_of_exactPairing (D₁' E₁ L₁ : D₁) (D₂' E₂ L₂ : D₂)
    [ExactPairing D₁' E₁] [ExactPairing D₂' E₂] :
    IsIso (externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂) := by
  let := ExactPairing.map F₁ D₁' E₁
  let := ExactPairing.map F₂ D₂' E₂
  have h := isIso_curry_tensorμ_comp_evaluation (F₁.obj D₁') (F₁.obj E₁) (F₁.obj L₁)
    (F₂.obj D₂') (F₂.obj E₂) (F₂.obj L₂)
  let u₁ := μ F₁ D₁' L₁ ≫ F₁.map (ihomObjIsoTensor D₁' E₁ L₁).inv
  let u₂ := μ F₂ D₂' L₂ ≫ F₂.map (ihomObjIsoTensor D₂' E₂ L₂).inv
  have hu : (u₁ ⊗ₘ u₂) ≫ externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂ =
      curry (tensorμ _ _ _ _ ≫
        (((α_ _ _ _).inv ≫ ε_ (F₁.obj D₁') (F₁.obj E₁) ▷ _ ≫ (λ_ _).hom) ⊗ₘ
          ((α_ _ _ _).inv ≫ ε_ (F₂.obj D₂') (F₂.obj E₂) ▷ _ ≫ (λ_ _).hom))) := by
    rw [eq_curry_iff, uncurry_natural_left, uncurry_externalIhomMap, tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom]
    congr 2
    · rw [MonoidalCategory.whiskerLeft_comp_assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
        ← F₁.map_comp, ← uncurry_eq, uncurry_ihomObjIsoTensor_inv,
        F₁.whiskerLeft_μ_comp_μ_comp_map_evaluation]
      rfl
    · rw [MonoidalCategory.whiskerLeft_comp_assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
        ← F₂.map_comp, ← uncurry_eq, uncurry_ihomObjIsoTensor_inv,
        F₂.whiskerLeft_μ_comp_μ_comp_map_evaluation]
      rfl
  have : IsIso (u₁ ⊗ₘ u₂) := by unfold u₁ u₂; infer_instance
  rw [← hu] at h
  exact IsIso.of_isIso_comp_left (u₁ ⊗ₘ u₂) _

end BaseCase

end MonoidalClosed

namespace Adjunction

open MonoidalClosed

section ProjectionIhom

variable {C C' : Type*} [Category* C] [Category* C'] [MonoidalCategory C] [MonoidalCategory C']
  [SymmetricCategory C] [SymmetricCategory C'] [MonoidalClosed C] [MonoidalClosed C']
  {F : C ⥤ C'} {L : C' ⥤ C} {R : C ⥤ C'} (adj : L ⊣ R)
  (π : ∀ (M : C') (N : C), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]

/-- The comparison `R (X ⟶ Y) ⟶ (F X ⟶ R Y)` of an adjunction `L ⊣ R` with an invertible
projection map `π : L M ⊗ N ⟶ L (M ⊗ F N)`: the transpose of
`F X ⊗ R (X ⟶ Y) ≅ R (X ⟶ Y) ⊗ F X ⟶ R ((X ⟶ Y) ⊗ X) ≅ R (X ⊗ (X ⟶ Y)) ⟶ R Y`, the tensor map
(`CategoryTheory.Adjunction.projectionTensorMap`) followed by the evaluation. For the
exceptional inverse image `g^! = R` it is `g^! RHom(X, Y) ⟶ RHom(g^* X, g^! Y)`. -/
noncomputable def projectionIhomMap (X Y : C) :
    R.obj ((ihom X).obj Y) ⟶ (ihom (F.obj X)).obj (R.obj Y) :=
  curry ((β_ _ _).hom ≫ adj.projectionTensorMap π _ X ≫ R.map ((β_ _ X).hom ≫ (ihom.ev X).app Y))


variable (hπ : ∀ {M M' : C'} (φ : M ⟶ M') (N : C),
  L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
include hπ


end ProjectionIhom

section TensorMap

variable {C C' : Type*} [Category* C] [Category* C'] [MonoidalCategory C] [MonoidalCategory C']
  [BraidedCategory C] [BraidedCategory C'] {F : C ⥤ C'} [F.Braided]

variable {L : C' ⥤ C} {R : C ⥤ C'} (adj : L ⊣ R)
  (π : ∀ (M : C') (N : C), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]
  (hπ : ∀ {M M' : C'} (φ : M ⟶ M') (N : C),
    L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
  (hπr : ∀ (M : C') {N N' : C} (φ : N ⟶ N'),
    L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ F.map φ))
  (hassoc : ∀ (M : C') (N N' : C), π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
    L.map (α_ M (F.obj N) (F.obj N')).hom =
      (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ Functor.OplaxMonoidal.δ F N N'))
include hπ hπr hassoc

end TensorMap

section MonoidalNatTrans

variable {C₂ C C' : Type*} [Category* C₂] [Category* C] [Category* C'] [MonoidalCategory C₂]
  [MonoidalCategory C] [MonoidalCategory C'] [BraidedCategory C] [BraidedCategory C']
  {G : C ⥤ C'} [G.LaxBraided] {F₂ : C₂ ⥤ C} {F₂' : C₂ ⥤ C'} [F₂.LaxMonoidal] [F₂'.LaxMonoidal]


end MonoidalNatTrans

section Step

variable {C₁ C₁' C₂ C C' : Type*} [Category* C₁] [Category* C₁'] [Category* C₂] [Category* C]
  [Category* C'] [MonoidalCategory C₁] [MonoidalCategory C₁'] [MonoidalCategory C₂]
  [MonoidalCategory C] [MonoidalCategory C'] [SymmetricCategory C₁] [SymmetricCategory C₁']
  [SymmetricCategory C] [SymmetricCategory C'] [MonoidalClosed C₁] [MonoidalClosed C₁']
  [MonoidalClosed C₂] [MonoidalClosed C] [MonoidalClosed C']
  {F₁ : C₁ ⥤ C} {F₂ : C₂ ⥤ C} {F₁' : C₁' ⥤ C'} {F₂' : C₂ ⥤ C'} [F₁.Braided] [F₂.LaxMonoidal]
  [F₁'.Braided] [F₂'.LaxMonoidal] {G : C ⥤ C'} [G.Braided] {G₁ : C₁ ⥤ C₁'}
  {L : C' ⥤ C} {R : C ⥤ C'} (adj : L ⊣ R)
  (π : ∀ (M : C') (N : C), L.obj M ⊗ N ⟶ L.obj (M ⊗ G.obj N)) [∀ M N, IsIso (π M N)]
  {L₁ : C₁' ⥤ C₁} {R₁ : C₁ ⥤ C₁'} (adj₁ : L₁ ⊣ R₁)
  (π₁ : ∀ (M : C₁') (N : C₁), L₁.obj M ⊗ N ⟶ L₁.obj (M ⊗ G₁.obj N)) [∀ M N, IsIso (π₁ M N)]
  (hπ : ∀ {M M' : C'} (φ : M ⟶ M') (N : C),
    L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ G.obj N))
  (hπ₁ : ∀ {M M' : C₁'} (φ : M ⟶ M') (N : C₁),
    L₁.map φ ▷ N ≫ π₁ M' N = π₁ M N ≫ L₁.map (φ ▷ G₁.obj N))
  (Ex : L₁ ⋙ F₁ ⟶ F₁' ⋙ L) [IsIso Ex] (ξ : TwoSquare F₁' L₁ L F₁)
  (hExξ : ∀ M : C₁', Ex.app M ≫ ξ.natTrans.app M = 𝟙 _)
  (κ : ∀ N : C₁, F₁'.obj (G₁.obj N) ⟶ G.obj (F₁.obj N)) [∀ N, IsIso (κ N)]

omit [MonoidalClosed C₁] [MonoidalClosed C₁'] [MonoidalClosed C₂] [MonoidalClosed C]
  [MonoidalClosed C'] [∀ M N, IsIso (π M N)] [∀ M N, IsIso (π₁ M N)] [IsIso Ex]
  [∀ N, IsIso (κ N)] [SymmetricCategory C₁] [SymmetricCategory C₁'] [SymmetricCategory C]
  [SymmetricCategory C'] [F₁.Braided] [F₁'.Braided] [G.Braided] in
/-- The compatibility of the base change map `Ex : L₁ ⋙ F₁ ⟶ F₁' ⋙ L` with the projection maps
`π₁` of `L₁` and `π` of `L`, through the comonoidal structures of `F₁`, `F₁'` and the comparison
maps `κ N : F₁' G₁ N ⟶ G F₁ N`. -/
def ProjectionExchange (δ₁' : ∀ M N : C₁', F₁'.obj (M ⊗ N) ⟶ F₁'.obj M ⊗ F₁'.obj N)
    (δ₁ : ∀ M N : C₁, F₁.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₁.obj N) : Prop :=
  ∀ (M : C₁') (N : C₁), F₁.map (π₁ M N) ≫ Ex.app (M ⊗ G₁.obj N) ≫
    L.map (δ₁' M (G₁.obj N)) ≫ L.map (F₁'.obj M ◁ κ N) =
      δ₁ (L₁.obj M) N ≫ Ex.app M ▷ F₁.obj N ≫ π (F₁'.obj M) (F₁.obj N)

variable (hEx : ProjectionExchange π π₁ Ex κ (Functor.OplaxMonoidal.δ F₁')
  (Functor.OplaxMonoidal.δ F₁))



end Step

end Adjunction

end CategoryTheory
