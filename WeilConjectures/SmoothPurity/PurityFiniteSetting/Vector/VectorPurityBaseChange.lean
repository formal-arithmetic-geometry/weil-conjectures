/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization

/-! # Canonical vector purity base-change equation

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: def-pur-vector-purity-base-change).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Pullback composition around the specified square, before tensoring with a Tate line.
Source: sk-prop-an, Step 4 (blueprint: def-pur-vector-purity-base-change). -/
def purityPullbackSquare (A : Type (u + 1)) [CommRing A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (K : Etale.DerivedCategoryModule A Y) :
    (RfPullback A g').obj ((RfPullback A f).obj K) ≅
      (RfPullback A f').obj ((RfPullback A g).obj K) :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g' f).symm.app K ≪≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f' g (g' ≫ f) sq.w).app K

/-- The actual pullback/twist associator, including the comparison for the pulled-back
bundle's coefficient. No map in this construction uses a purity isomorphism.
Source: sk-prop-an, Step 4 (blueprint: def-pur-vector-purity-base-change). -/
def purityBundleBaseChangeAssociator (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    {g : B' ⟶ B}
    {g' : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F}
    (sq : IsPullback g' (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) g)
    (K : Etale.DerivedCategoryModule A B) :
    (RfPullback A g').obj
        (Etale.vectorIntegrationCoefficient A N hA B d F ⊗
          (RfPullback A (VectorBundleZeroSection.π B d F)).obj K) ≅
      Etale.vectorIntegrationCoefficient A N hA B' d F' ⊗
        (RfPullback A (VectorBundleZeroSection.π B' d F')).obj
          ((RfPullback A g).obj K) :=
  Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g'
    (Etale.vectorIntegrationCoefficient A N hA B d F)
    ((RfPullback A (VectorBundleZeroSection.π B d F)).obj K) ≪≫
    ((purityPullbackSquare A sq (Etale.affineLinearBaseCoefficient A N hA B d) ≪≫
        (RfPullback A (VectorBundleZeroSection.π B' d F')).mapIso
          (Etale.vectorIntegrationBaseCoefficientPullback A N hA
            (purityTwistTransport A N hN hA) g hB d)) ⊗ᵢ purityPullbackSquare A sq K)

/-- The exceptional base-change equation for the independently normalized purity
maps of the original bundle and its pullback. Exchange is required invertible only
on the stated bounded constructible class. Source: sk-prop-an, Step 4
(blueprint: def-pur-vector-purity-base-change). -/
def PurityBaseChangeEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F) : Prop :=
  ∀ (B' : Scheme.{u}) [IsNoetherian B'] (g : B' ⟶ B)
    (hB' : IsUnit (N : Γ(B', ⊤)))
    (F' : B'.Modules) [F'.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B' d F')]
    [QuasiCompact (VectorBundleZeroSection.π B' d F')]
    (g' : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F)
    (sq : IsPullback g' (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) g),
    ∃ γ' : VectorPurityGamma A N hA B' d F',
    VectorPurityGammaNormalized A N hN hA B' hB' d F' γ' ∧
    ∀ K : (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B).FullSubcategory,
    IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K.obj) ∧
      (RfPullback A g').map (γ.app K.obj) ≫
          (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K.obj =
        (purityBundleBaseChangeAssociator A N hN hA hB d F F' sq K.obj).hom ≫
          γ'.app ((RfPullback A g).obj K.obj)

end WeilConjectures.PurityFiniteSetting
