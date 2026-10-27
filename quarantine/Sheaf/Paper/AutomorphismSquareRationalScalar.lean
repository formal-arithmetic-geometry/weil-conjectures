/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.AutomorphismConstructibleStageEquivalence

/-! # Scalar compatibility of the raw rational automorphism square

Source: latest blueprint lem-fix-weil-operations.proof.md, first paragraph.
(blueprint: lem-pod-automorphism-square-rational-scalar). -/

@[expose] public noncomputable section
set_option autoImplicit false
-- Use one endpoint normalization list for each heterogeneous composite.
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Only the prescribed object and tensor formulas are used below.
set_option allowUnsafeReducibility true in
attribute [local irreducible] automorphismStageIntegralSquare automorphismStageRationalSquare

private theorem dependent_heq {A : Type*} {B : A → Sort*}
    (f : (a : A) → B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  subst b
  rfl

private theorem map_heq
    {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    (F : C ⥤ D) {A A' B B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A'
  subst B'
  cases h
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_map_localized {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {K J : sfIntegralConstructibleCategory l E Y} (r : K ⟶ J) :
    HEq ((rationalDerivedPullback l E f).map
      ((sfRationalConstructibleLocalization l E Y).map r))
      ((sfRationalConstructibleLocalization l E X).map
        ((constructibleIntegralPullback l E f).map r)) := by
  simpa only [rationalDerivedPullback, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, ScalarLocalization.category] using
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K J r 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_map_localized
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})
    {K J : sfIntegralConstructibleCategory l E X} (r : K ⟶ J) :
    HEq ((sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
      ((sfRationalConstructibleLocalization l E X).map r))
      ((sfRationalConstructibleLocalization l L X).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map r)) := by
  have hs := (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 K J r 1
  simpa only [sfRationalScalarExtension, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, ScalarLocalization.category, map_one] using hs

/-- Localizing an integral commuting scalar square gives the corresponding equality
for the prescribed raw rational pullback comparisons.
Source: latest blueprint lem-fix-weil-operations.proof.md, first paragraph, pullback
comparison after extension of coefficients; raw rationalization definition
(blueprint: lem-pod-automorphism-square-rational-scalar).

Proof: every raw rational object has an integral object as its underlying object.
Use the prescribed object equations for rational pullback and scalar extension to
identify the six vertices of the scalar square with the localizations of their
integral counterparts. The specified rational square component is the localization
of the integral square component. Both single-pullback scalar comparisons have the
same property. On a localized integral arrow, the pure-tensor rules for pullback
and scalar extension, with scalar one, identify their maps with the localization
of the corresponding integral map, since coefficient inclusion preserves one.
Consequently both composites in the asserted equality are, after these endpoint
identifications, the localizations of the two composites in the hypothesis.
Functoriality of localization and that hypothesis prove equality. Cancel the
endpoint identifications. No rational-to-finite reduction is used. -/
theorem automorphismStageRationalSquare_scalar
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (S : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom)
    (hi : ∀ K : sfIntegralConstructibleCategory l E X,
      (integralScalarExtension l E L ι Y).map
          ((automorphismStageIntegralSquare l E S f eX eY h).hom.app K).hom ≫
        (integralPullbackScalarComparison l E L ι f
          ((constructibleIntegralPullback l E eX.hom).obj K)).hom.hom ≫
        (integralDerivedPullback l L f).map
          (integralPullbackScalarComparison l E L ι eX.hom K).hom.hom =
      (integralPullbackScalarComparison l E L ι eY.hom
          ((constructibleIntegralPullback l E f).obj K)).hom.hom ≫
        (integralDerivedPullback l L eY.hom).map
          (integralPullbackScalarComparison l E L ι f K).hom.hom ≫
        ((automorphismStageIntegralSquare l L S f eX eY h).hom.app
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K)).hom) :
    ∀ K : sfRationalConstructibleCategory l E X,
      (sfRationalScalarExtension l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
          ((automorphismStageRationalSquare l E S f eX eY h).hom.app K) ≫
        (rationalPullbackScalarComparison l E L ι f).hom.app
          ((rationalDerivedPullback l E eX.hom).obj K) ≫
        (rationalDerivedPullback l L f).map
          ((rationalPullbackScalarComparison l E L ι eX.hom).hom.app K) =
      (rationalPullbackScalarComparison l E L ι eY.hom).hom.app
          ((rationalDerivedPullback l E f).obj K) ≫
        (rationalDerivedPullback l L eY.hom).map
          ((rationalPullbackScalarComparison l E L ι f).hom.app K) ≫
        (automorphismStageRationalSquare l L S f eX eY h).hom.app
          ((sfRationalScalarExtension l E X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) := by
  intro K
  let T (Z : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Z
  let U (Z : Scheme.{u}) := sfRationalScalarExtension l E Z 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  have hp (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (J : sfRationalConstructibleCategory l A W) :
      (rationalDerivedPullback l A g).obj J =
        (sfRationalConstructibleLocalization l A V).obj
          ((constructibleIntegralPullback l A g).obj J.obj) :=
    (rationalDerivedPullback_existsUnique l A g).exists.choose_spec.2.1 J
  have hs (Z : Scheme.{u}) (J : sfRationalConstructibleCategory l E Z) :
      (sfRationalScalarExtension l E Z 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj J =
        (sfRationalConstructibleLocalization l L Z).obj ((T Z).obj J.obj) :=
    (sfRationalScalarExtension_existsUnique l E Z 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 J
  let aE := automorphismStageIntegralSquare l E S f eX eY h
  let aL := automorphismStageIntegralSquare l L S f eX eY h
  have haE : HEq ((automorphismStageRationalSquare l E S f eX eY h).hom.app K)
      ((sfRationalConstructibleLocalization l E Y).map (aE.hom.app K.obj)) := by
    simpa only [automorphismStageRationalSquare] using
      (automorphismStageRationalSquare_existsUnique l E S f eX eY h).exists.choose_spec K
  have h₁ := (map_heq (U Y) (by simp only [Functor.comp_obj, hp,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, hp,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) haE).trans
    (scalar_map_localized l E L ι Y (aE.hom.app K.obj))
  have h₂ := (rationalPullbackScalarComparison_existsUnique l E L ι f).exists.choose_spec
    ((rationalDerivedPullback l E eX.hom).obj K)
  have hobj : ((rationalDerivedPullback l E eX.hom).obj K).obj =
      (constructibleIntegralPullback l E eX.hom).obj K.obj :=
    congrArg ScalarLocalization.obj (hp E eX.hom K)
  have h₂' : HEq
      ((rationalPullbackScalarComparison l E L ι f).hom.app
        ((rationalDerivedPullback l E eX.hom).obj K))
      ((sfRationalConstructibleLocalization l L Y).map
        (integralPullbackScalarComparison l E L ι f
          ((constructibleIntegralPullback l E eX.hom).obj K.obj)).hom) := by
    have hb : HEq ((rationalPullbackScalarComparison l E L ι f).hom.app
        ((rationalDerivedPullback l E eX.hom).obj K))
        ((sfRationalConstructibleLocalization l L Y).map
          (integralPullbackScalarComparison l E L ι f
            ((rationalDerivedPullback l E eX.hom).obj K).obj).hom) := by
      simpa only [rationalPullbackScalarComparison] using h₂
    exact hb.trans (dependent_heq (fun J ↦ (sfRationalConstructibleLocalization l L Y).map
      (integralPullbackScalarComparison l E L ι f J).hom) hobj)
  have hα {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (J : sfRationalConstructibleCategory l E W) :
      HEq ((rationalPullbackScalarComparison l E L ι g).hom.app J)
        ((sfRationalConstructibleLocalization l L V).map
          (integralPullbackScalarComparison l E L ι g J.obj).hom) := by
    simpa only [rationalPullbackScalarComparison] using
      (rationalPullbackScalarComparison_existsUnique l E L ι g).exists.choose_spec J
  have h₃ := (map_heq (rationalDerivedPullback l L f)
    (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (hα eX.hom K)).trans
      (pullback_map_localized l L f
        (integralPullbackScalarComparison l E L ι eX.hom K.obj).hom)
  have h₄ := (rationalPullbackScalarComparison_existsUnique l E L ι eY.hom).exists.choose_spec
    ((rationalDerivedPullback l E f).obj K)
  have hobj₄ : ((rationalDerivedPullback l E f).obj K).obj =
      (constructibleIntegralPullback l E f).obj K.obj :=
    congrArg ScalarLocalization.obj (hp E f K)
  have h₄' : HEq
      ((rationalPullbackScalarComparison l E L ι eY.hom).hom.app
        ((rationalDerivedPullback l E f).obj K))
      ((sfRationalConstructibleLocalization l L Y).map
        (integralPullbackScalarComparison l E L ι eY.hom
          ((constructibleIntegralPullback l E f).obj K.obj)).hom) := by
    have hb : HEq ((rationalPullbackScalarComparison l E L ι eY.hom).hom.app
        ((rationalDerivedPullback l E f).obj K))
        ((sfRationalConstructibleLocalization l L Y).map
          (integralPullbackScalarComparison l E L ι eY.hom
            ((rationalDerivedPullback l E f).obj K).obj).hom) := by
      simpa only [rationalPullbackScalarComparison] using h₄
    exact hb.trans (dependent_heq (fun J ↦ (sfRationalConstructibleLocalization l L Y).map
      (integralPullbackScalarComparison l E L ι eY.hom J).hom) hobj₄)
  have h₅ := (map_heq (rationalDerivedPullback l L eY.hom)
    (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (hα f K)).trans
      (pullback_map_localized l L eY.hom
        (integralPullbackScalarComparison l E L ι f K.obj).hom)
  have h₆ := (automorphismStageRationalSquare_existsUnique l L S f eX eY h).exists.choose_spec
    ((U X).obj K)
  have hobj₆ : ((U X).obj K).obj = (T X).obj K.obj :=
    congrArg ScalarLocalization.obj (hs X K)
  have h₆' : HEq
      ((automorphismStageRationalSquare l L S f eX eY h).hom.app ((U X).obj K))
      ((sfRationalConstructibleLocalization l L Y).map
        (aL.hom.app ((T X).obj K.obj))) := by
    have hb : HEq ((automorphismStageRationalSquare l L S f eX eY h).hom.app ((U X).obj K))
        ((sfRationalConstructibleLocalization l L Y).map
          (aL.hom.app ((U X).obj K).obj)) := by
      simpa only [automorphismStageRationalSquare] using h₆
    exact hb.trans (dependent_heq (fun J ↦
      (sfRationalConstructibleLocalization l L Y).map (aL.hom.app J)) hobj₆)
  have hleft := heq_comp (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) h₁
    (heq_comp (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
      (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) h₂' h₃)
  have hright := heq_comp (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
    (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) h₄'
    (heq_comp (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) (by simp only [Functor.comp_obj, U, hp, hs, T,
      sfRationalConstructibleLocalization,
      ScalarLocalization.localization])
      (by simp only [Functor.comp_obj, U, hp, hs, T, sfRationalConstructibleLocalization,
      ScalarLocalization.localization]) h₅ h₆')
  have hint : (T Y).map (aE.hom.app K.obj) ≫
      (integralPullbackScalarComparison l E L ι f
        ((constructibleIntegralPullback l E eX.hom).obj K.obj)).hom ≫
      (constructibleIntegralPullback l L f).map
        (integralPullbackScalarComparison l E L ι eX.hom K.obj).hom =
    (integralPullbackScalarComparison l E L ι eY.hom
        ((constructibleIntegralPullback l E f).obj K.obj)).hom ≫
      (constructibleIntegralPullback l L eY.hom).map
        (integralPullbackScalarComparison l E L ι f K.obj).hom ≫
      aL.hom.app ((T X).obj K.obj) := by
    apply ObjectProperty.hom_ext (sfIntegralConstructible l L Y)
    exact hi K.obj
  have hloc := congrArg (sfRationalConstructibleLocalization l L Y).map hint
  simp only [Functor.map_comp] at hloc
  exact eq_of_heq (hleft.trans ((heq_of_eq hloc).trans hright.symm))

end WeilConjectures
