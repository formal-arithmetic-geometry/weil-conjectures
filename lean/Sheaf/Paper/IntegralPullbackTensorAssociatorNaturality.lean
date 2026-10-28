/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints
import all Sheaf.Paper.DerivedPullbackTensorConstraints

/-! # Naturality of the normalized integral tensor associator

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS, 07A4,
0941 and 0FPQ; the representative-independent derived naturality specialization
of the normalized completed associator.
(blueprint: lem-pur-integral-tensor-associator-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField

private theorem chosen_operation_spec {A : Sort*} {p : A → Prop}
    (h : ∃! a, p a) (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private theorem tensor_map_heq {C : Type*} [Category* C] (T : C × C ⥤ C)
    {A B D E A' B' D' E' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : D ⟶ E} {g' : D' ⟶ E'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (T.map (Prod.mkHom f g)) (T.map (Prod.mkHom f' g')) := by
  subst A' B' D' E'
  cases hf
  cases hg
  rfl

private theorem nested_comparison_naturality
    {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (e : T ⋙ R ≅ R.prod R ⋙ U)
    {A A' B B' C₀ C₀' : C} (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀') :
    R.map (T.map (Prod.mkHom (T.map (Prod.mkHom f g)) h)) ≫
        e.hom.app (T.obj (A', B'), C₀') ≫
        U.map (Prod.mkHom (e.hom.app (A', B')) (𝟙 _)) =
      e.hom.app (T.obj (A, B), C₀) ≫
        U.map (Prod.mkHom (e.hom.app (A, B)) (𝟙 _)) ≫
        U.map (Prod.mkHom (U.map (Prod.mkHom (R.map f) (R.map g))) (R.map h)) := by
  have he (X Y : C × C) (k : X ⟶ Y) :
      R.map (T.map k) ≫ e.hom.app Y =
        e.hom.app X ≫ U.map (Prod.mkHom (R.map k.1) (R.map k.2)) :=
    e.hom.naturality k
  rw [← Category.assoc, he]
  simp only [Category.assoc]
  congr 1
  rw [← U.map_comp, ← U.map_comp]
  congr 1
  ext
  · exact he (A, B) (A', B') (Prod.mkHom f g)
  · simp

private theorem nested_comparison_naturality_right
    {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (e : T ⋙ R ≅ R.prod R ⋙ U)
    {A A' B B' C₀ C₀' : C} (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀') :
    R.map (T.map (Prod.mkHom f (T.map (Prod.mkHom g h)))) ≫
        e.hom.app (A', T.obj (B', C₀')) ≫
        U.map (Prod.mkHom (𝟙 _) (e.hom.app (B', C₀'))) =
      e.hom.app (A, T.obj (B, C₀)) ≫
        U.map (Prod.mkHom (𝟙 _) (e.hom.app (B, C₀))) ≫
        U.map (Prod.mkHom (R.map f) (U.map (Prod.mkHom (R.map g) (R.map h)))) := by
  have he (X Y : C × C) (k : X ⟶ Y) :
      R.map (T.map k) ≫ e.hom.app Y =
        e.hom.app X ≫ U.map (Prod.mkHom (R.map k.1) (R.map k.2)) :=
    e.hom.naturality k
  rw [← Category.assoc, he]
  simp only [Category.assoc]
  congr 1
  rw [← U.map_comp, ← U.map_comp]
  congr 1
  ext
  · simp
  · exact he (B, C₀) (B', C₀') (Prod.mkHom g h)

private theorem faithful_associator_naturality
    {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) [R.Faithful] (T : C × C ⥤ C) (U : D × D ⥤ D)
    (e : T ⋙ R ≅ R.prod R ⋙ U)
    (a : ∀ A B C₀, T.obj (T.obj (A, B), C₀) ≅ T.obj (A, T.obj (B, C₀)))
    (b : ∀ A B C₀, U.obj (U.obj (A, B), C₀) ≅ U.obj (A, U.obj (B, C₀)))
    (hb : ∀ {A A' B B' C₀ C₀' : D} (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀'),
      U.map (Prod.mkHom (U.map (Prod.mkHom f g)) h) ≫ (b A' B' C₀').hom =
        (b A B C₀).hom ≫ U.map (Prod.mkHom f (U.map (Prod.mkHom g h))))
    (ha : ∀ A B C₀, R.map (a A B C₀).hom ≫ e.hom.app (A, T.obj (B, C₀)) ≫
      U.map (Prod.mkHom (𝟙 _) (e.hom.app (B, C₀))) =
        e.hom.app (T.obj (A, B), C₀) ≫
          U.map (Prod.mkHom (e.hom.app (A, B)) (𝟙 _)) ≫
            (b (R.obj A) (R.obj B) (R.obj C₀)).hom)
    {A A' B B' C₀ C₀' : C} (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀') :
    T.map (Prod.mkHom (T.map (Prod.mkHom f g)) h) ≫ (a A' B' C₀').hom =
      (a A B C₀).hom ≫ T.map (Prod.mkHom f (T.map (Prod.mkHom g h))) := by
  apply R.map_injective
  let d := e.app (A', T.obj (B', C₀')) ≪≫
    U.mapIso (Iso.prod (Iso.refl _) (e.app (B', C₀')))
  apply (cancel_mono d.hom).1
  change _ ≫ (e.hom.app (A', T.obj (B', C₀')) ≫
    U.map (Prod.mkHom (𝟙 _) (e.hom.app (B', C₀')))) =
    _ ≫ (e.hom.app (A', T.obj (B', C₀')) ≫
    U.map (Prod.mkHom (𝟙 _) (e.hom.app (B', C₀'))))
  simp only [Functor.map_comp, Category.assoc]
  rw [ha]
  have hl := congrArg (fun z ↦ z ≫ (b (R.obj A') (R.obj B') (R.obj C₀')).hom)
    (nested_comparison_naturality R T U e f g h)
  simp only [Category.assoc] at hl
  rw [hl, hb, nested_comparison_naturality_right R T U e f g h]
  simpa only [Category.assoc] using (congrArg
    (fun z ↦ z ≫ U.map (Prod.mkHom (R.map f)
      (U.map (Prod.mkHom (R.map g) (R.map h))))) (ha A B C₀)).symm

private theorem integral_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N P M' N' P' : sfIntegralConstructibleCategory l E W}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom ((constructibleIntegralTensor l E W).map (Prod.mkHom f g)) h) ≫
        (pullbackTensorIntegralAssociator l E W M' N' P').hom =
      (pullbackTensorIntegralAssociator l E W M N P).hom ≫
        (constructibleIntegralTensor l E W).map
          (Prod.mkHom f ((constructibleIntegralTensor l E W).map (Prod.mkHom g h))) := by
  have := (coherentReduction_fullyFaithful l E W).2
  apply faithful_associator_naturality (coherentReduction l E W)
    (constructibleIntegralTensor l E W) (pullbackTensorCalculus l E W).systemClosed.tensor
    (reduction_tensor l E W) (pullbackTensorIntegralAssociator l E W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.associator
  · intro M N P M' N' P' f g h
    exact @MonoidalCategory.associator_naturality _ _
      (pullbackTensorCalculus l E W).systemClosed.monoidal _ _ _ _ _ _ f g h
  · intro M N P
    unfold coherentReduction reduction_tensor pullbackTensorIntegralAssociator
    unfold NatIso.ofComponents
    dsimp only [Functor.comp_map, ObjectProperty.ι_map, Functor.comp_obj,
      Functor.prod_obj, ObjectProperty.ι_obj]
    exact (pullbackTensorIntegralAssociator_existsUnique l E W M N P).exists.choose_spec

/-- Naturality of the normalized integral tensor associator on arbitrary derived
morphisms.

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS, 07A4,
0941 and 0FPQ (blueprint: lem-pur-integral-tensor-associator-naturality).

Proof: coherent reduction is a functor with a natural reduction/tensor
comparison.  The nested comparison squares for the two bracketings follow from
the naturality of this comparison.  The defining reduction equation for the
normalized integral associator identifies both bracketings with the associator
of the strict coefficient-system monoidal structure.  That strict associator is
natural in all three variables.  Applying the faithful coherent reduction and
cancelling the comparison isomorphisms reflects the equality.  The completed
tensor and its action on pairs of morphisms preserve the derived-complete
constructible category, so the equation applies to arbitrary integral arrows,
including identities, zero arrows, and zero objects.
-/
theorem pullbackTensorIntegralAssociator_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    {M N P M' N' P' : sfIntegralConstructibleCategory l E W}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom ((constructibleIntegralTensor l E W).map (Prod.mkHom f g)) h) ≫
        (pullbackTensorIntegralAssociator l E W M' N' P').hom =
      (pullbackTensorIntegralAssociator l E W M N P).hom ≫
        (constructibleIntegralTensor l E W).map
          (Prod.mkHom f ((constructibleIntegralTensor l E W).map (Prod.mkHom g h))) := by
  exact integral_naturality l E W f g h

end WeilConjectures
