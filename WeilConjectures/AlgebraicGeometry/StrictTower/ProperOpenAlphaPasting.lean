/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
-- Vertical uses singleAlpha_restriction_normalized; horizontal uses singleAlpha_restriction.
-- Both restriction identities must coexist when these dependency branches are imported.
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaVerticalModules
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaHorizontalModules
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaBaseChangeModules

/-! # Intrinsic clopen alpha commutes with pasting and pullback before derivation

Source: Stacks Project, Tags 0F7C, 0F7D, 0F7F, 09AH and 09BN, with the arbitrary-ring
underived strict-tower refinement in the blueprint.
(blueprint: lem-cbc-proper-open-alpha-pasting)

Each law includes equality on module sheaves, on strict towers, on their unbounded
complexes, and on their ordinary unbounded derived categories. The two ordinary paths
are written with all inverse-image and open-extension compositors inserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The alphaVerticalPasted ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaVerticalPasted {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j) :
    moduleJ B j ⋙ modulePullback B (p₁ ≫ p₂) ⟶
      (modulePullback B r₂ ⋙ modulePullback B r₁) ⋙ moduleJ B k :=
  Functor.whiskerLeft (moduleJ B j) (moduleGComp B p₁ p₂).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (singleAlpha B i r₂ p₂ j h₂) (modulePullback B p₁) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback B r₂) (singleAlpha B k r₁ p₁ i h₁) ≫
    (Functor.associator _ _ _).inv

/-- The alphaVerticalOuter ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaVerticalOuter {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    moduleJ B j ⋙ modulePullback B (p₁ ≫ p₂) ⟶
      (modulePullback B r₂ ⋙ modulePullback B r₁) ⋙ moduleJ B k :=
  singleAlpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h ≫
    Functor.whiskerRight (moduleGComp B r₁ r₂).hom (moduleJ B k)

/-- The alphaHorizontalOuter ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaHorizontalOuter {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper q]
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) :
    (moduleJ B i ⋙ moduleJ B j) ⋙ modulePullback B q ⟶
      modulePullback B r ⋙ moduleJ B (k ≫ l) :=
  Functor.whiskerRight (openBetaModuleJComp B i j).hom (modulePullback B q) ≫
    singleAlpha B (k ≫ l) r q (i ≫ j) h

/-- The alphaHorizontalPasted ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaHorizontalPasted {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j) :
    (moduleJ B i ⋙ moduleJ B j) ⋙ modulePullback B q ⟶
      modulePullback B r ⋙ moduleJ B (k ≫ l) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (moduleJ B i) (singleAlpha B l p q j h₂) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (singleAlpha B k r p i h₁) (moduleJ B l) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback B r) (openBetaModuleJComp B k l).hom

/-- The alphaCubeOriginal ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaCubeOriginal {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i)
    (wk : d ≫ k = k₁ ≫ a)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) :
    moduleJ B i ⋙ (modulePullback B b ⋙ modulePullback B p₁) ⟶
      (modulePullback B c ⋙ modulePullback B r₁) ⋙ moduleJ B k₁ :=
  Functor.whiskerLeft (moduleJ B i) (moduleSquareG B a p₁ p b wp).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (singleAlpha B k r p i h) (modulePullback B a) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback B r) (openBetaModule B d k₁ k a wk sk).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (moduleSquareG B d r₁ r c wr).inv (moduleJ B k₁)

/-- The alphaCubeChanged ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaCubeChanged {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (b : T₁ ⟶ T) (c : S₁ ⟶ S)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wi : c ≫ i = i₁ ≫ b)
    (si : IsPullback c i₁ i b) :
    moduleJ B i ⋙ (modulePullback B b ⋙ modulePullback B p₁) ⟶
      (modulePullback B c ⋙ modulePullback B r₁) ⋙ moduleJ B k₁ :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (openBetaModule B c i₁ i b wi si).hom (modulePullback B p₁) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback B c) (singleAlpha B k₁ r₁ p₁ i₁ h₁) ≫
    (Functor.associator _ _ _).inv

attribute [local irreducible] G J

end AlgebraicGeometry.ProEtale.StrictTower
