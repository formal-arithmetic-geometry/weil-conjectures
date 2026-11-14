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
counit through the inverse compact-support exchange. All functors act on ordinary
unbounded categories. The occurrence of the left derived inverse image is canonically identified
with the exact degreewise inverse image by `leftDerivedUpperStarIsoMapDerivedCategory`. -/
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

/-- The base-change morphism on relative dualizing complexes: the exceptional comparison at
the coefficient unit, followed by the canonical inverse-image identification of that unit. -/
noncomputable def smoothDualizingBaseChangeMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
      (dualizingComplex A f) ⟶
    dualizingComplex A (pullback.snd f g) :=
  smoothExceptionalBaseChangeMap A f g (𝟙_ _) ≫
    (rightDerivedUpperShriek A (pullback.snd f g)).map
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom

/-- The canonical identification `g'^* f^* K ≅ f'^* g^* K`, formed from the inverse-image
composition isomorphisms and the equality of the two maps around the pullback square. -/
noncomputable def smoothSquarePullbackIso
    (A : Type (u + 1)) [CommRing A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K) ≅
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (pullback.fst f g) f).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (pullback.snd f g) g
      (pullback.fst f g ≫ f) (pullback.condition)).app K

/-- The tensor-domain identification in the smooth-duality square. Its first factor is the
canonical K-flat derived tensor-pullback comparison; the second is inverse-image composition. -/
noncomputable def smoothDualityTensorBaseChangeIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (g : S' ⟶ S) (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj
          (dualizingComplex A f)) ≅
    ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))).obj
      ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
        (dualizingComplex A f)) :=
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst f g)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
      (dualizingComplex A f) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).mapIso
      (smoothSquarePullbackIso A f g K)).app
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
          (dualizingComplex A f))

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

private lemma smooth_tensor_map_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [hPF : IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)]
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let := derivedBraidedCategory Λ X
    smoothTensorDualityMap Λ f hPF K =
      (β_ ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)
        (dualizingComplex Λ f)).hom ≫ dualizingComplexTensorMap Λ f K := by
  let := derivedBraidedCategory Λ X
  let := derivedBraidedCategory Λ S
  exact braided_tensor_mate (rightDerivedUpperShriekAdjunction Λ f)
    _ _ K _ (inv (((projectionMap (ModuleCat.{u + 1} Λ) f).app _).app K))
    ((rightDerivedUpperShriekAdjunction Λ f).counit.app (𝟙_ _))

private lemma mate_app_eq
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}
    (ξ : TwoSquare G L L' H) (M : D) :
    (mateEquiv adj adj' ξ).app M =
      (adj'.homEquiv _ _) (ξ.app (R.obj M) ≫ H.map (adj.counit.app M)) := by
  apply (adj'.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact mateEquiv_counit adj adj' ξ M

private lemma braided_tensor_square
    {C C' : Type*} [Category* C] [Category* C']
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory C'] [BraidedCategory C']
    (G : C ⥤ C') (P W Z : C) (P' W' Z' : C')
    (a : W ⊗ P ⟶ Z) (a' : W' ⊗ P' ⟶ Z') (b : G.obj W ⟶ W')
    (κ : G.obj P ⟶ P') (β : G.obj Z ⟶ Z')
    (δ : ∀ M N : C, G.obj (M ⊗ N) ⟶ G.obj M ⊗ G.obj N)
    (ha : G.map a ≫ β = δ W P ≫ b ▷ G.obj P ≫ W' ◁ κ ≫ a')
    (hδ : G.map (β_ P W).hom ≫ δ W P =
      δ P W ≫ (β_ (G.obj P) (G.obj W)).hom) :
    G.map ((β_ P W).hom ≫ a) ≫ β =
      δ P W ≫ κ ▷ G.obj W ≫ P' ◁ b ≫ (β_ P' W').hom ≫ a' := by
  rw [G.map_comp, Category.assoc, ha]
  rw [reassoc_of% hδ]
  simp only [← MonoidalCategory.tensorHom_def_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]

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

/-- Arbitrary base change for smooth ambient duality on ordinary unbounded etale
module derived categories, including the dualizing-complex and tensor compatibilities.
-/
theorem smooth_exceptional_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X S S' : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian S']
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (f : X ⟶ S) [IsSeparated f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (g : S' ⟶ S) :
    (∀ K : DerivedCategoryModule A S, IsIso (smoothExceptionalBaseChangeMap A f g K)) ∧
    IsIso (smoothDualizingBaseChangeMap A f g) ∧
    ∀ K : DerivedCategoryModule A S,
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
          (smoothTensorDualityMap A f
            (isIso_projectionMap_of_finite A f) K) ≫
        smoothExceptionalBaseChangeMap A f g K =
      (smoothDualityTensorBaseChangeIso A f g K).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))).map
          (smoothDualizingBaseChangeMap A f g) ≫
        smoothTensorDualityMap A (pullback.snd f g)
          (isIso_projectionMap_of_finite A (pullback.snd f g))
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) := by
  have hNS : IsUnit (N : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro s hs
    simpa only [map_natCast] using hInvertible s
  have : HasInvertibleExponent A S := ⟨N, hN, hA, hNS⟩
  have : HasInvertibleExponent A X := HasInvertibleExponent.of_hom f
  have hBC := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    A f d (IsPullback.of_hasPullback f g)
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)
  have hMap (K : DerivedCategoryModule A S) :
      smoothExceptionalBaseChangeMap A f g K =
        (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app K := by
    symm
    simpa only [smoothExceptionalBaseChangeMap, rightDerivedUpperShriekBaseChangeMap,
      NatIso.isIso_inv_app, Functor.id_obj, Functor.comp_obj] using
      mate_app_eq
      (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction A (pullback.snd f g))
      (inv (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g))) K
  refine ⟨?_, ?_, ?_⟩
  · intro K
    rw [hMap]
    infer_instance
  · unfold smoothDualizingBaseChangeMap
    rw [hMap]
    infer_instance
  · intro K
    let := derivedBraidedCategory A X
    let := derivedBraidedCategory A (pullback f g)
    have hδ := leftDerivedUpperStar_map_braiding_hom_δ (ModuleCat.{u + 1} A)
      (pullback.fst f g)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
      (dualizingComplex A f)
    have ht := braided_tensor_square
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
      (dualizingComplex A f)
      ((rightDerivedUpperShriek A f).obj K)
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
      (dualizingComplex A (pullback.snd f g))
      ((rightDerivedUpperShriek A (pullback.snd f g)).obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
      (dualizingComplexTensorMap A f K)
      (dualizingComplexTensorMap A (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
      (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f g))
      (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback f g).toCommSq K)
      ((rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app K)
      (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
        (pullback.fst f g) M N).hom)
      (dualizing_tensor_base_change A f g K) hδ
    have hφ := smooth_tensor_map_eq A f K
    have hφ' := smooth_tensor_map_eq A (pullback.snd f g)
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)
    simpa only [hφ, hφ', dualizingComplexTensorMap,
      smoothDualityTensorBaseChangeIso, smoothSquarePullbackIso,
      smoothDualizingBaseChangeMap, hMap, dualizingComplexBaseChangeMap,
      derivedSquareUpperStarIsoInvApp, derivedSquareUpperStarIso,
      Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, NatTrans.comp_app, Iso.app_hom,
      derivedTensor, curriedTensor,
      Functor.mapIso_hom, Category.assoc] using ht

end AlgebraicGeometry.Etale
