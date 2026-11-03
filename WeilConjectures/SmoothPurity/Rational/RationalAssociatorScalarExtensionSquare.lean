/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import all WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import WeilConjectures.SmoothPurity.Integral.IntegralAssociatorScalarExtensionSquare

/-! # Naturality and scalar extension of the rational associator

Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace WeilConjectures

attribute [local irreducible] Scheme.residueField

/-- A bifunctor sends componentwise heterogeneously equal arrows to heterogeneously equal
arrows. -/
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

/-- Naturality of a tensor comparison, applied to a left-nested tensor. -/
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

/-- Naturality of a tensor comparison, applied to a right-nested tensor. -/
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

/-- An associator transported along a faithful functor from a natural associator is natural. -/
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
  apply (cancel_mono (e.app (A', T.obj (B', C₀')) ≪≫
    U.mapIso (Iso.prod (Iso.refl _) (e.app (B', C₀')))).hom).1
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [ha]
  have hl := congrArg (fun z ↦ z ≫ (b (R.obj A') (R.obj B') (R.obj C₀')).hom)
    (nested_comparison_naturality R T U e f g h)
  simp only [Category.assoc] at hl
  rw [hl, hb, nested_comparison_naturality_right R T U e f g h]
  simpa only [Category.assoc] using (congrArg
    (fun z ↦ z ≫ U.map (Prod.mkHom (R.map f)
      (U.map (Prod.mkHom (R.map g) (R.map h))))) (ha A B C₀)).symm

/-- The integral associator is natural in its three arguments. -/
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

/-- The objects of the rational tensor are the integral tensor objects. -/
private theorem rationalDerivedTensor_obj_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (MN : sfRationalConstructibleCategory l E W × sfRationalConstructibleCategory l E W) :
    (rationalDerivedTensor l E W).obj MN =
      ScalarLocalization.mk ((constructibleIntegralTensor l E W).obj (MN.1.obj, MN.2.obj)) :=
  (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 MN

/-- The rational tensor of two pure tensors is the pure tensor of the product scalar and the
integral tensor. -/
private theorem rationalDerivedTensor_map_tmul_heq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (A A' B B' : sfRationalConstructibleCategory l E W)
    (f : A.obj ⟶ A'.obj) (g : B.obj ⟶ B'.obj)
    (a c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((rationalDerivedTensor l E W).map (Prod.mkHom
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f : A ⟶ A')
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] g : B ⟶ B')))
      ((a * c) ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralTensor l E W).map (Prod.mkHom f g)) := by
  obtain ⟨b, hb, hp⟩ := (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2 A A' B B'
  rw [rationalDerivedTensor, hb]
  exact hp f g a c

/-- The rational tensor is additive in each variable. -/
private theorem rationalDerivedTensor_bilinear
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (A A' B B' : sfRationalConstructibleCategory l E W) :
    ∃ b : (A ⟶ A') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
        (B ⟶ B') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
        ((rationalDerivedTensor l E W).obj (A, B) ⟶ (rationalDerivedTensor l E W).obj (A', B')),
      ∀ f g, (rationalDerivedTensor l E W).map (Prod.mkHom f g) = b f g := by
  obtain ⟨b, hb, -⟩ := (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2 A A' B B'
  exact ⟨b, hb⟩

/-- The rational associator is natural in its three arguments.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-rational-pullback-tensor-associator-natural).
Proof: the integral associator is natural, since coherent reduction is faithful and conjugates
it to the natural system associator. Rational maps are sums of localized integral maps and the
rational tensor is computed on localized pure tensors, so naturality localizes. -/
theorem rationalAssociator_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M M' N N' P P' : sfRationalConstructibleCategory l E W}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom ((rationalDerivedTensor l E W).map (Prod.mkHom f g)) h) ≫
      (pullbackTensorRationalAssociator l E W M' N' P').hom =
    (pullbackTensorRationalAssociator l E W M N P).hom ≫
      (rationalDerivedTensor l E W).map
        (Prod.mkHom f ((rationalDerivedTensor l E W).map (Prod.mkHom g h))) := by
  let I := constructibleIntegralTensor l E W
  let R := Padic.coefficientExtensionIntegers l E
  have ho := rationalDerivedTensor_obj_eq l E W
  let b (A A' B B' : sfRationalConstructibleCategory l E W) :=
    (rationalDerivedTensor_bilinear l E W A A' B B').choose
  have hb (A A' B B' : sfRationalConstructibleCategory l E W) (f : A ⟶ A') (g : B ⟶ B') :
      (rationalDerivedTensor l E W).map (Prod.mkHom f g) = b A A' B B' f g :=
    (rationalDerivedTensor_bilinear l E W A A' B B').choose_spec f g
  have hp := rationalDerivedTensor_map_tmul_heq l E W
  have hlobj (A B C : sfRationalConstructibleCategory l E W) :
      (rationalDerivedTensor l E W).obj ((rationalDerivedTensor l E W).obj (A, B), C) =
        ScalarLocalization.mk (I.obj (I.obj (A.obj, B.obj), C.obj)) := by
    rw [ho, ho]
  have hrobj (A B C : sfRationalConstructibleCategory l E W) :
      (rationalDerivedTensor l E W).obj (A, (rationalDerivedTensor l E W).obj (B, C)) =
        ScalarLocalization.mk (I.obj (A.obj, I.obj (B.obj, C.obj))) := by
    rw [ho, ho]
  induction f using TensorProduct.induction_on with
  | zero =>
    simp only [hb, map_zero, LinearMap.zero_apply, Limits.zero_comp,
      Limits.comp_zero]
  | add f f' hf hf' =>
    simpa only [hb, map_add, LinearMap.add_apply, Preadditive.add_comp,
      Preadditive.comp_add] using congrArg₂ (· + ·) hf hf'
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero =>
      simp only [hb, map_zero, LinearMap.zero_apply, Limits.zero_comp,
        Limits.comp_zero]
    | add g g' hg hg' =>
      simpa only [hb, map_add, LinearMap.add_apply, Preadditive.add_comp,
        Preadditive.comp_add] using congrArg₂ (· + ·) hg hg'
    | tmul c g =>
      induction h using TensorProduct.induction_on with
      | zero =>
        simp only [hb, map_zero, Limits.zero_comp, Limits.comp_zero]
      | add h h' hh hh' =>
        simpa only [hb, map_add, LinearMap.add_apply, Preadditive.add_comp,
          Preadditive.comp_add] using congrArg₂ (· + ·) hh hh'
      | tmul d h =>
        have hleft := (tensor_map_heq (rationalDerivedTensor l E W) (ho (M, N)) (ho (M', N'))
          rfl rfl
          (hp M M' N N' f g a c) HEq.rfl).trans
            (hp (ScalarLocalization.mk (I.obj (M.obj, N.obj)))
              (ScalarLocalization.mk (I.obj (M'.obj, N'.obj))) P P'
              (I.map (Prod.mkHom f g)) h (a * c) d)
        have hright := (tensor_map_heq (rationalDerivedTensor l E W) rfl rfl (ho (N, P))
          (ho (N', P'))
          HEq.rfl (hp N N' P P' g h c d)).trans
            (hp M M' (ScalarLocalization.mk (I.obj (N.obj, P.obj)))
              (ScalarLocalization.mk (I.obj (N'.obj, P'.obj)))
              f (I.map (Prod.mkHom g h)) a (c * d))
        have hl := heq_comp (hlobj M N P) (hlobj M' N' P') (hrobj M' N' P') hleft
          (pullbackTensorRationalAssociator_existsUnique l E W M' N' P').exists.choose_spec
        have hr := heq_comp (hlobj M N P) (hrobj M N P) (hrobj M' N' P')
          (pullbackTensorRationalAssociator_existsUnique l E W M N P).exists.choose_spec hright
        apply eq_of_heq
        refine hl.trans ((heq_of_eq ?_).trans hr.symm)
        have key : ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E)) *
              (a * c * d)) ⊗ₜ[R] (I.map (Prod.mkHom (I.map (Prod.mkHom f g)) h) ≫
                (pullbackTensorIntegralAssociator l E W M'.obj N'.obj P'.obj).hom) =
            ((a * (c * d)) * 1) ⊗ₜ[R]
              ((pullbackTensorIntegralAssociator l E W M.obj N.obj P.obj).hom ≫
                I.map (Prod.mkHom f (I.map (Prod.mkHom g h)))) := by
          rw [integral_naturality l E W f g h, one_mul, mul_one, mul_assoc]
        exact (ScalarLocalization.composition_tmul R (sfIntegralConstructibleCategory l E W)
          (Padic.coefficientExtensionUniformizer l E) _ _ _
          (pullbackTensorIntegralAssociator l E W M'.obj N'.obj P'.obj).hom
          (I.map (Prod.mkHom (I.map (Prod.mkHom f g)) h)) 1 (a * c * d)).trans
          (key.trans (ScalarLocalization.composition_tmul R
            (sfIntegralConstructibleCategory l E W) (Padic.coefficientExtensionUniformizer l E)
            _ _ _ (I.map (Prod.mkHom f (I.map (Prod.mkHom g h))))
            (pullbackTensorIntegralAssociator l E W M.obj N.obj P.obj).hom
            (a * (c * d)) 1).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational scalar extension sends a localized integral arrow to the localization of its
integral scalar extension. -/
private theorem scalarMap_integral_local
    (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (X : Scheme.{u})
    (A B : sfRationalConstructibleCategory l E X)
    (A₀ B₀ : sfIntegralConstructibleCategory l E X)
    (hA : A = (sfRationalConstructibleLocalization l E X).obj A₀)
    (hB : B = (sfRationalConstructibleLocalization l E X).obj B₀)
    (f : A ⟶ B) (f₀ : A₀ ⟶ B₀)
    (hf : HEq f ((sfRationalConstructibleLocalization l E X).map f₀)) :
    HEq ((sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map f)
      ((sfRationalConstructibleLocalization l F X).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι X).map f₀)) := by
  cases hA
  cases hB
  cases hf
  simpa only [map_one, sfRationalConstructibleLocalization, ScalarLocalization.localization,
    sfRationalScalarExtension, sfConstructibleIntegralScalarExtension] using
    sfRationalScalarExtension_map_tmul l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι A₀ B₀ f₀ 1

/-- The rational associator commutes with the prescribed rational tensor scalar comparison.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: every object and both tensor comparisons are localizations of their integral versions,
and scalar extension sends a localized arrow to the localization of its integral scalar
extension. Both composites are the localization of the two composites of
`integralAssociatorScalarExtensionSquare`. -/
theorem rationalAssociatorScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :
    (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        (pullbackTensorRationalAssociator l E W M N P).hom ≫
      (rationalTensorScalarComparison l E L ι W).hom.app
        (M, (rationalDerivedTensor l E W).obj (N, P)) ≫
      (rationalDerivedTensor l L W).map
        (Prod.mkHom (𝟙 ((sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M))
          ((rationalTensorScalarComparison l E L ι W).hom.app (N, P))) =
    (rationalTensorScalarComparison l E L ι W).hom.app
        ((rationalDerivedTensor l E W).obj (M, N), P) ≫
      (rationalDerivedTensor l L W).map
        (Prod.mkHom ((rationalTensorScalarComparison l E L ι W).hom.app (M, N))
          (𝟙 ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P))) ≫
      (pullbackTensorRationalAssociator l L W
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          P)).hom := by
  let S := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let G := sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let Q := sfRationalConstructibleLocalization l L W
  let TE := rationalDerivedTensor l E W
  let TF := rationalDerivedTensor l L W
  let TI := constructibleIntegralTensor l E W
  let TJ := constructibleIntegralTensor l L W
  have hs (K : sfRationalConstructibleCategory l E W) : G.obj K = Q.obj (S.obj K.obj) :=
    sfRationalScalarExtension_obj l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K
  have hoE := rationalDerivedTensor_obj_eq l E W
  have hoL := rationalDerivedTensor_obj_eq l L W
  have hid (K : sfRationalConstructibleCategory l E W) :
      HEq (𝟙 (G.obj K)) (Q.map (𝟙 (S.obj K.obj))) := by
    rw [hs K, Q.map_id]
  have hc (K K' : sfRationalConstructibleCategory l E W) :=
    (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec K K'
  have hu (K K' : sfRationalConstructibleCategory l E W) :
      G.obj (TE.obj (K, K')) = Q.obj (S.obj (TI.obj (K.obj, K'.obj))) := by
    rw [hs, hoE]
  have hv (K K' : sfRationalConstructibleCategory l E W) :
      TF.obj (G.obj K, G.obj K') = Q.obj (TJ.obj (S.obj K.obj, S.obj K'.obj)) := by
    rw [hoL, hs, hs]
    rfl
  have o1 : G.obj (TE.obj (TE.obj (M, N), P)) =
      Q.obj (S.obj (TI.obj (TI.obj (M.obj, N.obj), P.obj))) := by
    rw [hs, hoE, hoE]
  have o2 : G.obj (TE.obj (M, TE.obj (N, P))) =
      Q.obj (S.obj (TI.obj (M.obj, TI.obj (N.obj, P.obj)))) := by
    rw [hs, hoE, hoE]
  have o3 : TF.obj (G.obj M, G.obj (TE.obj (N, P))) =
      Q.obj (TJ.obj (S.obj M.obj, S.obj (TI.obj (N.obj, P.obj)))) := by
    rw [hoL, hu, hs]
    rfl
  have o4 : TF.obj (G.obj M, TF.obj (G.obj N, G.obj P)) =
      Q.obj (TJ.obj (S.obj M.obj, TJ.obj (S.obj N.obj, S.obj P.obj))) := by
    rw [hoL, hv, hs]
    rfl
  have o5 : TF.obj (G.obj (TE.obj (M, N)), G.obj P) =
      Q.obj (TJ.obj (S.obj (TI.obj (M.obj, N.obj)), S.obj P.obj)) := by
    rw [hoL, hu, hs]
    rfl
  have o6 : TF.obj (TF.obj (G.obj M, G.obj N), G.obj P) =
      Q.obj (TJ.obj (TJ.obj (S.obj M.obj, S.obj N.obj), S.obj P.obj)) := by
    rw [hoL, hv, hs]
    rfl
  have hA : TE.obj (TE.obj (M, N), P) = (sfRationalConstructibleLocalization l E W).obj
      (TI.obj (TI.obj (M.obj, N.obj), P.obj)) := by
    rw [hoE, hoE]
    rfl
  have hB : TE.obj (M, TE.obj (N, P)) = (sfRationalConstructibleLocalization l E W).obj
      (TI.obj (M.obj, TI.obj (N.obj, P.obj))) := by
    rw [hoE, hoE]
    rfl
  have h1 := scalarMap_integral_local l E L ι W _ _ _ _ hA hB _ _
    (pullbackTensorRationalAssociator_existsUnique l E W M N P).exists.choose_spec
  have h2 : HEq ((rationalTensorScalarComparison l E L ι W).hom.app (M, TE.obj (N, P)))
      (Q.map (integralTensorScalarComparison l E L ι W M.obj (TI.obj (N.obj, P.obj))).hom) :=
    (hc M (TE.obj (N, P))).trans (by rw [hoE])
  have h3 : HEq (TF.map (Prod.mkHom (𝟙 (G.obj M))
        ((rationalTensorScalarComparison l E L ι W).hom.app (N, P))))
      (Q.map (TJ.map (Prod.mkHom (𝟙 (S.obj M.obj))
        (integralTensorScalarComparison l E L ι W N.obj P.obj).hom))) :=
    ((tensor_map_heq TF (hs M) (hs M) (hu N P) (hv N P) (hid M) (hc N P)).trans
      (rationalDerivedTensor_map_tmul_heq l L W _ _ _ _ (𝟙 (S.obj M.obj))
        (integralTensorScalarComparison l E L ι W N.obj P.obj).hom 1 1)).trans
      (by
        rw [one_mul]
        rfl)
  have h4 : HEq ((rationalTensorScalarComparison l E L ι W).hom.app (TE.obj (M, N), P))
      (Q.map (integralTensorScalarComparison l E L ι W (TI.obj (M.obj, N.obj)) P.obj).hom) :=
    (hc (TE.obj (M, N)) P).trans (by rw [hoE])
  have h5 : HEq (TF.map (Prod.mkHom ((rationalTensorScalarComparison l E L ι W).hom.app (M, N))
        (𝟙 (G.obj P))))
      (Q.map (TJ.map (Prod.mkHom (integralTensorScalarComparison l E L ι W M.obj N.obj).hom
        (𝟙 (S.obj P.obj))))) :=
    ((tensor_map_heq TF (hu M N) (hv M N) (hs P) (hs P) (hc M N) (hid P)).trans
      (rationalDerivedTensor_map_tmul_heq l L W _ _ _ _
        (integralTensorScalarComparison l E L ι W M.obj N.obj).hom (𝟙 (S.obj P.obj)) 1 1)).trans
      (by
        rw [one_mul]
        rfl)
  have h6 : HEq (pullbackTensorRationalAssociator l L W (G.obj M) (G.obj N) (G.obj P)).hom
      (Q.map (pullbackTensorIntegralAssociator l L W (S.obj M.obj) (S.obj N.obj)
        (S.obj P.obj)).hom) := by
    have hM := congrArg ScalarLocalization.obj (hs M)
    have hN := congrArg ScalarLocalization.obj (hs N)
    have hP := congrArg ScalarLocalization.obj (hs P)
    refine (pullbackTensorRationalAssociator_existsUnique l L W
      (G.obj M) (G.obj N) (G.obj P)).exists.choose_spec.trans ?_
    rw [hM, hN, hP]
    rfl
  have hL := heq_comp o1 o2 o4 h1 (heq_comp o2 o3 o4 h2 h3)
  have hR := heq_comp o1 o5 o4 h4 (heq_comp o5 o6 o4 h5 h6)
  apply eq_of_heq
  refine hL.trans ((heq_of_eq ?_).trans hR.symm)
  simp only [← Functor.map_comp]
  exact (Q.map_comp _ _).symm.trans
    (congrArg Q.map (integralAssociatorScalarExtensionSquare l E L ι W M.obj N.obj P.obj))

end WeilConjectures
