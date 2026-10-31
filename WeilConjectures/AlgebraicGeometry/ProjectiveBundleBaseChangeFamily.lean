/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleFrameModels
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleCoefficientComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleBaseChangeTheta

/-! # Per-morphism normalized projective-bundle base-change data
Source: Stacks Project, Constructions, Tag 01O3.
(blueprint: lem-pur-projective-bundle-base-change-family). -/

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

/-- Per-morphism normalized comparisons, before proving their coherence laws.
Source: Stacks Project, Tag 01O3.
(blueprint: lem-pur-projective-bundle-base-change-family). -/
structure ProjectiveBundleBaseChangeFamily {n : ℕ}
    (M : ProjectiveBundleFrameModels.{u} n) where
  baseChange : ∀ {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (hF : projectiveBundleRank B n F) (hF' : projectiveBundleRank B' n F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F),
      ProjectiveBundleBaseChangeDatum (M.bundle B F hF) (M.bundle B' F' hF') g e

/-- Assemble the explicit coefficient comparison, its actual relative-Proj map, and the
quotient-line comparison into a per-morphism family.
Source: Stacks Project, Tags 01OB and 01O3.
(blueprint: lem-pur-projective-bundle-base-change-family). -/
theorem exists_projectiveBundleBaseChangeFamily {n : ℕ}
    (M : ProjectiveBundleFrameModels.{u} n) :
    Nonempty (ProjectiveBundleBaseChangeFamily M) := by
  classical
  refine ⟨{ baseChange := fun {B B' F F'} hF hF' g e ↦ Classical.choice ?_ }⟩
  let : F.IsFiniteLocallyFreeOfRank (n + 1) := hF
  let : F'.IsFiniteLocallyFreeOfRank (n + 1) := hF'
  let : F.IsLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F (n + 1)
  let : F'.IsLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F' (n + 1)
  obtain ⟨b, hb⟩ := exists_projectiveBundleCoefficientComparison g e
    (M.bundle B F hF).A (M.bundle B' F' hF').A
  obtain ⟨theta, htheta⟩ := exists_projectiveBundleBaseChangeTheta
    (M.bundle B F hF) (M.bundle B' F' hF') g e b hb
  exact ⟨{
    comparison := b
    generator := fun {U U'} h x ↦ hb U U' h x
    map := b.relProjComparison
    map_eq := rfl
    over := b.isPullback.w
    theta := theta
    theta_quotient := htheta
  }⟩

end AlgebraicGeometry
