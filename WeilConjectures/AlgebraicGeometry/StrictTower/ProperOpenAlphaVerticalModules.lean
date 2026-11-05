/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.CategoryTheory.ExactDerivedPasting.ExactDerivedPastingComponents
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import WeilConjectures.AlgebraicGeometry.StrictTower.SingleAlphaRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing

/-! # Intrinsic alpha vertical identity on module sheaves

Source: Stacks Project, Tag 0F7C, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-proper-open-alpha-vertical-modules)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
  moduleSquareG fixedRestriction

open CategoryTheory.ExactDerivedPasting
set_option linter.unusedSimpArgs false

@[irreducible] private def nativeVerticalData {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    NativeVerticalData B A C E B₀ D F where
  K := moduleJ B k
  L := moduleJ B i
  J := moduleJ B j
  R₁ := modulePullback B r₁
  R₂ := modulePullback B r₂
  R := modulePullback B (r₁ ≫ r₂)
  P₁ := modulePullback B p₁
  P₂ := modulePullback B p₂
  P := modulePullback B (p₁ ≫ p₂)
  a₁ := singleAlpha B k r₁ p₁ i h₁
  a₂ := singleAlpha B i r₂ p₂ j h₂
  ao := singleAlpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h
  cp := moduleGComp B p₁ p₂
  cr := moduleGComp B r₁ r₂
  h := singleAlpha_vertical B k i j r₁ r₂ p₁ p₂ h₁ h₂ h

-- Capture the public derived-category instances before installing the tower instance.

section DerivedTransport
attribute [local instance] exactPairAdditive
attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] G J alpha beta gComp jComp squareG

end DerivedTransport

end AlgebraicGeometry.ProEtale.StrictTower
