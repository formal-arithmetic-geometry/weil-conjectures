/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The projective-bundle identity comparison on pullback sections
Source: Stacks Project, Sheaves, Tag 0097.
(blueprint: lem-pur-projective-bundle-pullback-identity-section). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The specified pullback identity sends the pulled section to its original section.
Source: Stacks Project, Tag 0097.
Proof: the left-adjoint comparison preserves the adjunction unit. The ordinary pullback
identity is conjugate to the direct-image identity; its unit equation evaluates to the
identity section. Composing these two equations gives the assertion.
(blueprint: lem-pur-projective-bundle-pullback-identity-section). -/
theorem projectiveBundlePullbackId_section
    (X : Scheme.{u}) (F : X.Modules) (U : X.Opens) (m : Γ(F, U)) :
    ((projectiveBundlePullbackId X).hom.app F).app U
      (projectiveBundlePullbackSection (𝟙 X) m) = m := by
  have ht := Adjunction.unit_leftAdjointUniq_hom_app
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X)))
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)) F
  have hte := congrArg (fun q ↦ q.app U m) ht
  have hu := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom F
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at hu
  have hue := congrArg (fun q ↦ q.app U m) hu
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    ConcreteCategory.comp_apply] at hte hue
  change ((Scheme.Modules.pullbackId X).hom.app F).app U
    (((projectiveBundleTensorPullbackIso (𝟙 X)).hom.app F).app U
      (projectiveBundlePullbackSection (𝟙 X) m)) = m
  exact (congrArg
    (fun t ↦ ((Scheme.Modules.pullbackId X).hom.app F).app ((𝟙 X) ⁻¹ᵁ U) t)
    hte).trans (hue.symm.trans (by rfl))

end AlgebraicGeometry
