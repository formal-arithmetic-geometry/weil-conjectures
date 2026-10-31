/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothDualityBaseChangeCompat

/-! # Arbitrary base change for smooth ambient duality

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md
(blueprint: prop-asd-smooth-base-change).

The exceptional comparison is the transpose of the inverse compact-support exchange
followed by the pulled-back counit. The coefficient-unit and tensor comparisons below
are the canonical ones; no orientation or arbitrary comparison is chosen.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Fix the canonical universe model before elaborating the derived functors.
attribute [local instance] Scheme.Etale.essentiallySmall

attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory

/-- The canonical exceptional base-change morphism, obtained by transposing the pulled-back
counit through the inverse compact-support exchange. Source: blueprint
sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md, first proof paragraph
(blueprint: prop-asd-smooth-base-change). All functors act on ordinary unbounded categories.
The occurrence of the left derived inverse image is canonically identified with the
exact degreewise inverse image by `leftDerivedUpperStarIsoMapDerivedCategory`. -/
noncomputable def smoothExceptionalBaseChangeMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
      ((rightDerivedUpperShriek A f).obj K) ⟶
    (rightDerivedUpperShriek A (pullback.snd f g)).obj
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) := by
  letI := isIso_rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)
  exact (rightDerivedUpperShriekAdjunction A
    (pullback.snd f g)).homEquiv _ _
    (inv ((rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app
      ((rightDerivedUpperShriek A f).obj K)) ≫
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
        ((rightDerivedUpperShriekAdjunction A f).counit.app K))

private lemma braided_tensor_mate
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (P W : C) (K Q : D)
    (π : F.obj (W ⊗ P) ⟶ Q ⊗ K) (ε : Q ⟶ 𝟙_ D) :
    adj.homEquiv _ _ (F.map (β_ P W).hom ≫ π ≫
        (β_ Q K).hom ≫ (K ◁ ε) ≫ (ρ_ K).hom) =
      (β_ P W).hom ≫ (adj.homEquiv _ _ (π ≫ (ε ▷ K)) ≫ G.map (λ_ K).hom) := by
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

private lemma unit_tensor_base_change
    {Cx Cy Cx' Cy' : Type*} [Category* Cx] [Category* Cy]
    [Category* Cx'] [Category* Cy']
    [MonoidalCategory Cx] [MonoidalCategory Cy]
    [MonoidalCategory Cx'] [MonoidalCategory Cy']
    (F R : Cy ⥤ Cx) (F' R' : Cy' ⥤ Cx') (Ga : Cx ⥤ Cx') (Gb : Cy ⥤ Cy')
    (τ : ∀ M N : Cy, R.obj M ⊗ F.obj N ⟶ R.obj (M ⊗ N))
    (τ' : ∀ M N : Cy', R'.obj M ⊗ F'.obj N ⟶ R'.obj (M ⊗ N))
    (β : R ⋙ Ga ⟶ Gb ⋙ R')
    (δa : ∀ M N : Cx, Ga.obj (M ⊗ N) ⟶ Ga.obj M ⊗ Ga.obj N)
    (δb : ∀ M N : Cy, Gb.obj (M ⊗ N) ⟶ Gb.obj M ⊗ Gb.obj N)
    (κ : ∀ N : Cy, Ga.obj (F.obj N) ⟶ F'.obj (Gb.obj N))
    (e : Gb.obj (𝟙_ Cy) ⟶ 𝟙_ Cy')
    (hτ : ∀ M N : Cy,
      Ga.map (τ M N) ≫ β.app (M ⊗ N) ≫ R'.map (δb M N) =
        δa (R.obj M) (F.obj N) ≫ β.app M ▷ Ga.obj (F.obj N) ≫
          R'.obj (Gb.obj M) ◁ κ N ≫ τ' (Gb.obj M) (Gb.obj N))
    (hτ' : ∀ {M M' : Cy'} (φ : M ⟶ M') (N : Cy'),
      R'.map φ ▷ F'.obj N ≫ τ' M' N = τ' M N ≫ R'.map (φ ▷ N))
    (he : ∀ N : Cy, δb (𝟙_ Cy) N ≫ e ▷ Gb.obj N ≫ (λ_ (Gb.obj N)).hom =
      Gb.map (λ_ N).hom) (N : Cy) :
    Ga.map (τ (𝟙_ Cy) N ≫ R.map (λ_ N).hom) ≫ β.app N =
      δa (R.obj (𝟙_ Cy)) (F.obj N) ≫
        (β.app (𝟙_ Cy) ≫ R'.map e) ▷ Ga.obj (F.obj N) ≫
        R'.obj (𝟙_ Cy') ◁ κ N ≫ τ' (𝟙_ Cy') (Gb.obj N) ≫
        R'.map (λ_ (Gb.obj N)).hom := by
  rw [Ga.map_comp, Category.assoc]
  erw [β.naturality]
  change Ga.map (τ (𝟙_ Cy) N) ≫ β.app (𝟙_ Cy ⊗ N) ≫
    R'.map (Gb.map (λ_ N).hom) = _
  rw [← he, R'.map_comp, R'.map_comp]
  rw [reassoc_of% (hτ (𝟙_ Cy) N)]
  rw [← reassoc_of% (hτ' e (Gb.obj N))]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, whisker_exchange_assoc]

private lemma exceptional_tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) (M N : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
        (rightDerivedUpperShriekTensorMap f M N) ≫
      (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app
        (M ⊗ N) ≫
      (rightDerivedUpperShriek A (pullback.snd f g)).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g M N).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst f g)
      ((rightDerivedUpperShriek A f).obj M)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)).hom ≫
      (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app M ▷
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)) ≫
      ((rightDerivedUpperShriek A (pullback.snd f g)).obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)) ◁
          (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
            (IsPullback.of_hasPullback f g).toCommSq N) ≫
      rightDerivedUpperShriekTensorMap (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap A
    (IsPullback.of_hasPullback f g)
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  exact Adjunction.projectionTensorMap_mateEquiv
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (pullback.snd f g))
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) (pullback.snd f g)).app M).app N)
    (fun φ N ↦ NatTrans.congr_app
      ((projectionMap (ModuleCat.{u + 1} A) (pullback.snd f g)).naturality φ) N)
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
      (pullback.fst f g) M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback f g).toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g))
    (inv (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N

private lemma dualizing_tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
        (dualizingComplexTensorMap A f K) ≫
      (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app K =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst f g)
      (dualizingComplex A f)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).hom ≫
      (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f g)) ▷
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) ≫
      (dualizingComplex A (pullback.snd f g)) ◁
        (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback f g).toCommSq K) ≫
      dualizingComplexTensorMap A (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) := by
  exact unit_tensor_base_change
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    (rightDerivedUpperShriek A f)
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor
    (rightDerivedUpperShriek A (pullback.snd f g))
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    (rightDerivedUpperShriekTensorMap f)
    (rightDerivedUpperShriekTensorMap (pullback.snd f g))
    (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g))
    (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
      (pullback.fst f g) M N).hom)
    (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g M N).hom)
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback f g).toCommSq N)
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom
    (exceptional_tensor_base_change A f g)
    (Adjunction.projectionTensorMap_naturality_left
      (rightDerivedUpperShriekAdjunction A (pullback.snd f g))
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) (pullback.snd f g)).app M).app N)
      (fun φ N ↦ NatTrans.congr_app
      ((projectionMap (ModuleCat.{u + 1} A) (pullback.snd f g)).naturality φ) N))
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom (ModuleCat.{u + 1} A) g) K

end AlgebraicGeometry.Etale
