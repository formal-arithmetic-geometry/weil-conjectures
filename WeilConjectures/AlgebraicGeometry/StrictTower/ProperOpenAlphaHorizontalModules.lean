/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaRestriction
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
import all WeilConjectures.CategoryTheory.ExactDerivedPasting.ExactDerivedPastingComponents

/-! # Intrinsic alpha horizontal identity on module sheaves

Source: Stacks Project, Tag 0F7D, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-proper-open-alpha-horizontal-modules)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSimpArgs false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
attribute [local irreducible] moduleSquareG openBetaModule openBetaModuleJComp

open CategoryTheory.ExactDerivedPasting

@[irreducible] private def nativeHorizontalData {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) :
    NativeHorizontalData B A C E B₀ D F where
  K := moduleJ B k
  L := moduleJ B l
  KL := moduleJ B (k ≫ l)
  V := moduleJ B i
  J := moduleJ B j
  VJ := moduleJ B (i ≫ j)
  R := modulePullback B r
  P := modulePullback B p
  Q := modulePullback B q
  a₁ := singleAlpha B k r p i h₁
  a₂ := singleAlpha B l p q j h₂
  ao := singleAlpha B (k ≫ l) r q (i ≫ j) h
  ci := (openBetaModuleJComp B i j).hom
  ck := (openBetaModuleJComp B k l).hom
  h := singleAlpha_horizontal B k l i j r p q h₁ h₂ h

-- Capture the public derived-category instances before installing the tower instance.

section DerivedTransport
attribute [local instance] exactPairAdditive
attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] G J alpha beta gComp jComp squareG

end DerivedTransport

end AlgebraicGeometry.ProEtale.StrictTower
