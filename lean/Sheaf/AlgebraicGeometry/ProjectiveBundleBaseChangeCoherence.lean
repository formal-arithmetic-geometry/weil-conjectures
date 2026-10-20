/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleFrameModels


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

Proof: for B' to B and an isomorphism F' to g^*F, use affine pullback sections
and symmetric-algebra base change to construct the graded coefficient map sending
v to e^{-1}(1 tensor v). It preserves every degree because each piece is spanned
by products of degree-one generators. On base restrictions the maps agree on
scalars and generators, hence everywhere by the symmetric universal property.
They give PullbackData for the two graded algebras. Its relative-Proj comparison
is the required map, with its over-base equation. On pulled-back frame charts,
send the pulled-back free generator T_i to T'_i. The ratios pull back to the
same ratios, so the line maps and their inverses glue. Their quotient equation
holds on all frame vectors, hence holds on every affine section and globally.
For the identity, the coefficient map fixes every generator and scalar, so its
Proj comparison is the identity. The glued line map also fixes every generator,
which gives theta_id with the canonical pullback identity. For a composite of
two base maps both coefficient maps send each generator to its twice-pulled-back
image, under the canonical pullback composition comparison. Thus they agree on
all homogeneous fractions. Relative-Proj chart uniqueness gives the map equality.
Both theta composites carry each pulled-back T_i to the same generator, so they
agree on a cover. The canonical adjoint comparisons in the statement are the
ones respecting the pullback units; their identity and associativity equations
therefore give precisely the displayed theta_comp, with no flatness assumption.
Proof irrelevance removes the dependence on rank witnesses. -/
theorem exists_projectiveBundleBaseChangeCoherence {n : ℕ}
    (M : ProjectiveBundleFrameModels.{u} n) :
    Nonempty (ProjectiveBundleBaseChangeCoherence M) := by
  sorry

end AlgebraicGeometry
