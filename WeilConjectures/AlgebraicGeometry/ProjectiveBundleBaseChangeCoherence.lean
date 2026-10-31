/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleFrameModels
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleBaseChangeFamily
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleBaseChangeLaws
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleBaseChangeMapUniqueness
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientEpi
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePullbackUnitLaws

/-! # Coherence of projective-bundle base change

Source: Stacks Project, Tags 01OB, 01O3, 01OE.
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

/-- Coherent coefficient-pullback comparisons for a family of normalized frame models.
Their maps and degree-one theta isomorphisms satisfy identity and composition laws.
Source: Stacks Project, Tag 01O3
(blueprint: lem-pur-projective-bundle-base-change-coherence). -/
structure ProjectiveBundleBaseChangeCoherence {n : ℕ} (M : ProjectiveBundleFrameModels.{u} n)
    where
  baseChange : ∀ {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (hF : projectiveBundleRank B n F) (hF' : projectiveBundleRank B' n F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F),
      ProjectiveBundleBaseChangeDatum (M.bundle B F hF) (M.bundle B' F' hF') g e
  baseChange_id : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).map =
      𝟙 (M.bundle B F hF).A.data.relProj
  baseChange_theta_id : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).theta =
      (projectiveBundlePullbackCongr (baseChange_id B F hF)).app (M.bundle B F hF).L ≪≫
        (projectiveBundlePullbackId (M.bundle B F hF).A.data.relProj).app (M.bundle B F hF).L
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
      (projectiveBundlePullbackCongr (baseChange_comp h₀ h₁ h₂ g h e e')).app
        (M.bundle B₀ F₀ h₀).L ≪≫
        ((projectiveBundlePullbackComp (baseChange h₁ h₂ h e').map
          (baseChange h₀ h₁ g e).map).app (M.bundle B₀ F₀ h₀).L).symm ≪≫
        (Scheme.Modules.tensorPullback (baseChange h₁ h₂ h e').map).mapIso
          (baseChange h₀ h₁ g e).theta ≪≫ (baseChange h₁ h₂ h e').theta

/-- Base-change coherence of the normalized symmetric-algebra frame models.
Source: Stacks Project, Constructions, Tag 01O3, including the degree-one theta;
steps 6--9 of lem-pur-projective-bundle-tautological-geometry.
(blueprint: lem-pur-projective-bundle-base-change-coherence).

Proof: choose per-morphism normalized data by exists_projectiveBundleBaseChangeFamily
(coefficient maps transported from the canonical symmetric pullback data, their
relative-Proj comparison, and a quotient-compatible theta). The identity map law holds
because the normalized identity comparison fixes scalars and generators, hence is the
identity on every relative-Proj chart. The canonical identity line map satisfies the
quotient square by the proved tensor-pullback unit laws. The map composition law and the
quotient square of the canonical composite line map are exists_projectiveBundleBaseChangeLaws.
The normalized quotient is epic, so a theta is determined by its quotient square; this
cancellation identifies the chosen theta with each canonical composite, giving theta_id
and theta_comp, with no flatness assumption. -/
theorem exists_projectiveBundleBaseChangeCoherence {n : ℕ}
    (M : ProjectiveBundleFrameModels.{u} n) :
    Nonempty (ProjectiveBundleBaseChangeCoherence M) := by
  obtain ⟨I⟩ := exists_projectiveBundleBaseChangeFamily M
  obtain ⟨C⟩ := exists_projectiveBundleBaseChangeLaws I
  exact ⟨{
    baseChange := I.baseChange
    baseChange_id := fun B F hF ↦ projectiveBundleBaseChangeMap_identity
      (M.bundle B F hF) (I.baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm)
    baseChange_theta_id := fun B F hF ↦ projectiveBundleBaseChangeTheta_unique
      (M.bundle B F hF) (M.bundle B F hF) _ _ _ _ _ _
      (I.baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).theta_quotient
      (projectiveBundleThetaQuotientLaw_identity (M.bundle B F hF) _
        (projectiveBundleBaseChangeMap_identity (M.bundle B F hF) _)
        (I.baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).over)
    baseChange_comp := C.baseChange_comp
    baseChange_theta_comp := fun h₀ h₁ h₂ g h e e' ↦
      projectiveBundleBaseChangeTheta_unique _ _ _ _ _ _ _ _
        (I.baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
          (projectiveBundlePullbackComp h g).app _)).theta_quotient
        (C.baseChange_theta_comp h₀ h₁ h₂ g h e e')
  }⟩

end AlgebraicGeometry
