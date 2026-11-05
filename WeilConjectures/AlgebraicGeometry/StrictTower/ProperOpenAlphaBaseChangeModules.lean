/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.CategoryTheory.ExactDerivedPasting.ExactDerivedPastingComponents
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-! # Intrinsic alpha baseChange identity on module sheaves

Source: Stacks Project, Tag 0F7F, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-proper-open-alpha-base-change-modules)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
attribute [local irreducible] moduleSquareG openBetaModule openBetaModuleJComp

open CategoryTheory.ExactDerivedPasting
set_option linter.unusedSimpArgs false

@[irreducible] private def nativeCubeData {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (hp : IsPullback a p₁ p b) (hr : IsPullback d r₁ r c) :
    NativeCubeData B V S W T V₁ S₁ W₁ T₁ where
  K := moduleJ B k
  V := moduleJ B i
  R := modulePullback B r
  P := modulePullback B p
  K₁ := moduleJ B k₁
  V₁ := moduleJ B i₁
  R₁ := modulePullback B r₁
  P₁ := modulePullback B p₁
  A := modulePullback B a
  B' := modulePullback B b
  C' := modulePullback B c
  D := modulePullback B d
  ao := singleAlpha B k r p i h
  a₁ := singleAlpha B k₁ r₁ p₁ i₁ h₁
  bk := openBetaModule B d k₁ k a wk sk
  bi := openBetaModule B c i₁ i b wi si
  sp := moduleSquareG B a p₁ p b wp
  sr := moduleSquareG B d r₁ r c wr
  h := singleAlpha_baseChange B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si hp hr

-- Capture the public derived-category instances before installing the tower instance.

section DerivedTransport
attribute [local instance] exactPairAdditive
attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] G J alpha beta gComp jComp squareG

end DerivedTransport

end AlgebraicGeometry.ProEtale.StrictTower
