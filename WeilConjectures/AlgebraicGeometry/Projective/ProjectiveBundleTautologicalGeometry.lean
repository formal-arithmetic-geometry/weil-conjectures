/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebra
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleBaseChangeCoherence
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleCoordinateGeometry
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleRankZero

/-! # Finite locally free projective bundles and tautological geometry

Source: Stacks Project, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
end AlgebraicGeometry

namespace AlgebraicGeometry

/-- A coherent family of the projective-bundle constructions. Module isomorphisms to a
pullback are included in the indexing to make the identity and composition equations typed
without pretending that iterated pullbacks are definitionally equal.
Source: Stacks, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleTautologicalSystem (n : ℕ) where
  bundle : ∀ (B : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F), ProjectiveBundleRealization B F
  invertible : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (bundle B F hF).L.IsInvertible
  proper : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    IsProper (bundle B F hF).A.data.relProjHom
  frame : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
      ProjectiveBundleFrameChart (bundle B F hF) n U e
  pullback_rank : ∀ (B B' : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F) (g : B' ⟶ B),
      projectiveBundleRank B' n ((Scheme.Modules.tensorPullback g).obj F)
  baseChange : ∀ {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (hF : projectiveBundleRank B n F) (hF' : projectiveBundleRank B' n F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F),
      ProjectiveBundleBaseChangeDatum (bundle B F hF) (bundle B' F' hF') g e
  baseChange_id : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).map =
      𝟙 (bundle B F hF).A.data.relProj
  baseChange_theta_id : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).theta =
      (projectiveBundlePullbackCongr (baseChange_id B F hF)).app (bundle B F hF).L ≪≫
        (projectiveBundlePullbackId (bundle B F hF).A.data.relProj).app (bundle B F hF).L
  baseChange_comp : ∀ {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules}
    {F₂ : B₂.Modules} (h₀ : projectiveBundleRank B₀ n F₀)
    (h₁ : projectiveBundleRank B₁ n F₁) (h₂ : projectiveBundleRank B₂ n F₂)
    (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀)
    (e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁),
      (baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀)).map =
      (baseChange h₁ h₂ h e').map ≫
        (baseChange h₀ h₁ g e).map
  baseChange_theta_comp : ∀ {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules}
    {F₂ : B₂.Modules} (h₀ : projectiveBundleRank B₀ n F₀)
    (h₁ : projectiveBundleRank B₁ n F₁) (h₂ : projectiveBundleRank B₂ n F₂)
    (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀)
    (e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁),
      (baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀)).theta =
      (projectiveBundlePullbackCongr (baseChange_comp h₀ h₁ h₂ g h e e')).app (bundle B₀ F₀ h₀).L ≪≫
        ((projectiveBundlePullbackComp (baseChange h₁ h₂ h e').map
          (baseChange h₀ h₁ g e).map).app (bundle B₀ F₀ h₀).L).symm ≪≫
        (Scheme.Modules.tensorPullback (baseChange h₁ h₂ h e').map).mapIso
          (baseChange h₀ h₁ g e).theta ≪≫ (baseChange h₁ h₂ h e').theta
  coordinate : ∀ (K : Type u) [Field K], ProjectiveBundleCoordinateGeometry K n
  rank_zero : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (_hzero : n = 0), ∃ _e : (bundle B F hF).L ≅
      (Scheme.Modules.tensorPullback (bundle B F hF).A.data.relProjHom).obj F,
      IsIso (bundle B F hF).A.data.relProjHom

end AlgebraicGeometry
