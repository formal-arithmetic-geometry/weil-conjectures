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

end WeilConjectures.PurityFiniteSetting
