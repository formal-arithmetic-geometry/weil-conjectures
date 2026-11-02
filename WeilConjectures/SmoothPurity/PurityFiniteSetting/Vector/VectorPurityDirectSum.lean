/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange

/-! # Ordered vector purity direct-sum equation

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: def-pur-vector-purity-direct-sum).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

-- Preserve the single-degree embedding while comparing its tensor-unit objects.
-- Unfolding it here expands the derived localization before comparing the sheaves.
attribute [local irreducible] _root_.DerivedCategory.singleFunctors

/-- The unique symmetric-algebra extension of a map of degree-one generators.
Source: the symmetric-algebra universal property in sk-prop-an, direct-sum geometry
(blueprint: def-pur-vector-purity-direct-sum). -/
def puritySymmetricAlgebraMap (B : Scheme.{u}) (F G : B.Modules) (j : G ⟶ F) :
    SymmetricAlgebraSheaf.algebra G ⟶ SymmetricAlgebraSheaf.algebra F :=
  (exists_quasiCoherentSymmetricAlgebra_core B G (SymmetricAlgebraSheaf.algebra F)
    (j ≫ SymmetricAlgebraSheaf.inclusion F)).exists.choose

/-- The canonical contravariant vector-bundle map induced by a map of generators.
The algebra map is the unique symmetric-algebra extension, and relative Spec applies
its recorded anti-equivalence. Source: sk-prop-an, direct-sum geometry
(blueprint: def-pur-vector-purity-direct-sum). -/
def purityBundleMap (B : Scheme.{u}) [IsNoetherian B] (r s : ℕ)
    (F G : B.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (j : G ⟶ F) :
    VectorBundleZeroSection.scheme B r F ⟶ VectorBundleZeroSection.scheme B s G :=
  ((VectorBundleZeroSection.antiEquivalence B).inverse.map
    (ObjectProperty.homMk
      (X := VectorBundleZeroSection.algebraObject B s G)
      (Y := VectorBundleZeroSection.algebraObject B r F)
      (puritySymmetricAlgebraMap B F G j))).unop.hom.left

/-- Binary sums of module sheaves carry their usual biproduct structure.
Source: sk-prop-an, F₁ direct-sum F₂ (blueprint: def-pur-vector-purity-direct-sum). -/
instance purityModuleBiproducts (B : Scheme.{u}) : HasFiniteBiproducts B.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Additive ranks use the ordered tensor-power associator. The base case uses the
coefficient UNIT OBJECT, and each successor is the monoidal associator.
Source: sk-prop-an, Step 5 (blueprint: def-pur-vector-purity-direct-sum). -/
def purityPowerAdd (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) (r : ℕ) : ∀ s : ℕ,
    Etale.affineLinearBaseCoefficient A N hA B (r + s) ≅
      Etale.affineLinearBaseCoefficient A N hA B r ⊗
        Etale.affineLinearBaseCoefficient A N hA B s
  | 0 => (ρ_ _).symm ≪≫
      (Iso.refl _ ⊗ᵢ (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).symm)
  | s + 1 => (purityPowerAdd A N hA B r s ⊗ᵢ Iso.refl _) ≪≫ α_ _ _ _

/-- The compact-support composition is formed from an actual triangle of
compactifications and its canonical independence comparisons.
Source: sk-prop-an, Step 5; lower-shriek composition construction
(blueprint: def-pur-vector-purity-direct-sum). -/
def purityCompactComposition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (q : X ⟶ Y) (p : Y ⟶ Z) (h : X ⟶ Z) (w : q ≫ p = h)
    [HasCompactification q] [HasCompactification p] [HasCompactification h]
    [QuasiCompact q] [QuasiCompact p]
    (c : Compactification p) (e : Compactification (q ≫ c.i)) :
    RfShriek A h ≅ RfShriek A q ⋙ RfShriek A p := by
  subst h
  exact (Etale.rightDerivedLowerShriekIso A (c.comp e)).symm ≪≫
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso A c e).symm ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso A e.restrict) _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIso A c)

/-- The exceptional compositor is the right-adjoint mate of the actual compact-support
composition, with the two Brown adjunctions and their counits retained.
Source: sk-prop-an, Step 5 (blueprint: def-pur-vector-purity-direct-sum). -/
def compositeCompactSupportMate (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (q : X ⟶ Y) (p : Y ⟶ Z) (h : X ⟶ Z) (w : q ≫ p = h)
    [HasCompactification q] [HasCompactification p] [HasCompactification h]
    [QuasiCompact q] [QuasiCompact p]
    (c : Compactification p) (e : Compactification (q ≫ c.i)) :
    RfUpper A h ≅ RfUpper A p ⋙ RfUpper A q :=
  Adjunction.rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction A h).ofNatIsoLeft
      (purityCompactComposition A q p h w c e))
    ((Etale.rightDerivedUpperShriekAdjunction A q).comp
      (Etale.rightDerivedUpperShriekAdjunction A p))

/-- The unit component of gamma, with the actual pullback-unit and right-unitor maps.
Source: sk-prop-an, omega_pi specialization (blueprint: def-pur-vector-purity-direct-sum). -/
def purityGammaUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F) :
    Etale.vectorIntegrationCoefficient A N hA B d F ⟶
      (RfUpper A (VectorBundleZeroSection.π B d F)).obj (𝟙_ _) :=
  (ρ_ (Etale.vectorIntegrationCoefficient A N hA B d F)).inv ≫
    (Etale.vectorIntegrationCoefficient A N hA B d F ◁
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π B d F)).inv) ≫
    γ.app (𝟙_ _)

/-- The ordered tensor/pullback associator for a composite and two ranks. All maps
are tensorators, the additive Tate associator and inverse-image composition.
Source: sk-prop-an, Step 5 (blueprint: def-pur-vector-purity-direct-sum). -/
def purityOrderedAssociator (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) {X Y B : Scheme.{u}}
    (q : X ⟶ Y) (p : Y ⟶ B) (h : X ⟶ B) (w : q ≫ p = h)
    (r s : ℕ) (K : Etale.DerivedCategoryModule A B) :
    (RfPullback A h).obj (Etale.affineLinearBaseCoefficient A N hA B (r + s)) ⊗
        (RfPullback A h).obj K ≅
      (RfPullback A q).obj ((RfPullback A p).obj
          (Etale.affineLinearBaseCoefficient A N hA B r)) ⊗
        (RfPullback A q).obj
          ((RfPullback A p).obj (Etale.affineLinearBaseCoefficient A N hA B s) ⊗
            (RfPullback A p).obj K) :=
  (((RfPullback A h).mapIso (purityPowerAdd A N hA B r s) ≪≫
      Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h
        (Etale.affineLinearBaseCoefficient A N hA B r)
        (Etale.affineLinearBaseCoefficient A N hA B s) ≪≫
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p h w.symm).app _ ⊗ᵢ
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p h w.symm).app _)) ⊗ᵢ
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p h w.symm).app K) ≪≫
    α_ _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) q _ _).symm)

/-- The factor purity for q is obtained by actual exceptional base change of the
first bundle's unit component, then the canonical dualizing tensor morphism. It is
independent of the purity map of the sum. Source: sk-prop-an, Steps 4--5
(blueprint: def-pur-vector-purity-direct-sum). -/
def puritySecondFactorGamma (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B]
    (r s : ℕ) (F G : B.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    [HasCompactification (VectorBundleZeroSection.π B r F)]
    (γ : VectorPurityGamma A N hA B r F)
    {X : Scheme.{u}} (q : X ⟶ VectorBundleZeroSection.scheme B s G)
    (j : X ⟶ VectorBundleZeroSection.scheme B r F) [HasCompactification q]
    [QuasiCompact q]
    (sq : IsPullback j q (VectorBundleZeroSection.π B r F)
      (VectorBundleZeroSection.π B s G))
    (L : Etale.DerivedCategoryModule A (VectorBundleZeroSection.scheme B s G)) :
    (RfPullback A q).obj ((RfPullback A (VectorBundleZeroSection.π B s G)).obj
        (Etale.affineLinearBaseCoefficient A N hA B r)) ⊗
      (RfPullback A q).obj L ⟶ (RfUpper A q).obj L :=
  (((purityPullbackSquare A sq _).inv ≫
      (RfPullback A j).map (purityGammaUnit A N hA B r F γ) ≫
      Etale.dualizingComplexBaseChangeMap A sq) ▷ (RfPullback A q).obj L) ≫
    Etale.dualizingComplexTensorMap A q L

/-- Direct sums use the symmetric-algebra projections, their actual compactification
triangle and its right-adjoint mate. The equation is the ordered Step-5 composite,
including both inverse-purity factors and the Tate/pullback associator.
Source: sk-prop-an, Step 5 (blueprint: def-pur-vector-purity-direct-sum). -/
def PurityDirectSumEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (r : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank r]
    [HasCompactification (VectorBundleZeroSection.π B r F)]
    (γ : VectorPurityGamma A N hA B r F) : Prop :=
  ∀ (s : ℕ) (G : B.Modules) [G.IsFiniteLocallyFreeOfRank s],
    ∃ hsum : (F ⊞ G).IsFiniteLocallyFreeOfRank (r + s),
    letI := hsum
    let p := VectorBundleZeroSection.π B s G
    let h := VectorBundleZeroSection.π B (r + s) (F ⊞ G)
    let j := purityBundleMap B (r + s) r (F ⊞ G) F biprod.inl
    let q := purityBundleMap B (r + s) s (F ⊞ G) G biprod.inr
    ∀ [HasCompactification p] [HasCompactification h]
      [HasCompactification q] [QuasiCompact q] [QuasiCompact p],
    ∀ (w : q ≫ p = h)
      (sq : IsPullback j q (VectorBundleZeroSection.π B r F) p),
      ∀ (c : Compactification p) (e : Compactification (q ≫ c.i)),
      ∃ (γG : VectorPurityGamma A N hA B s G)
        (γsum : VectorPurityGamma A N hA B (r + s) (F ⊞ G)),
      VectorPurityGammaNormalized A N hN hA B hB s G γG ∧
      VectorPurityGammaNormalized A N hN hA B hB (r + s) (F ⊞ G) γsum ∧
      ∀ K : (Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} A) B).FullSubcategory,
      γsum.app K.obj =
        (purityOrderedAssociator A N hA q p h w r s K.obj).hom ≫
          ((RfPullback A q).obj ((RfPullback A p).obj
            (Etale.affineLinearBaseCoefficient A N hA B r)) ◁
              (RfPullback A q).map (γG.app K.obj)) ≫
          puritySecondFactorGamma A N hA B r s F G γ q j sq
            ((RfUpper A p).obj K.obj) ≫
          (compositeCompactSupportMate A q p h w c e).inv.app K.obj

end WeilConjectures.PurityFiniteSetting
