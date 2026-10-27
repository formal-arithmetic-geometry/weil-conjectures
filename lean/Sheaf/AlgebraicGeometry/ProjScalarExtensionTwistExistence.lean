/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData
import Sheaf.RingTheory.HomogeneousLocalizationScalarExtension
import Sheaf.Algebra.Module.GradedLocalizationScalarExtension
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists

/-! # ProjScalarExtensionTwistExistence

Source: Stacks Project, Constructions, Tags 01N2, 01MY and 01MZ.
(blueprint: lem-sfb-proj-scalar-extension-twist-existence). -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The normalized twist comparison exists, independently of its uniqueness and coherence.
Source: Stacks Project, Constructions, Tags 01N2 and 01MY.

Proof: On D_+(f), identify pullback sections by the affine pullback-sections theorem.
Scalar extension of homogeneous localization identifies the degree-zero coefficient ring;
scalar extension of the degree-j graded module piece then gives the balanced equivalence
u tensor c mapped to c psi(u). Its inverse is induced by the inverse coefficient and module
comparisons. Affine tilde--sections adjunction transports this equivalence to an isomorphism
of quasi-coherent sheaves. On intersections, both restrictions send a/f^m to
psi(a) psi(g)^m / psi(fg)^m, so affine faithfulness identifies the restricted morphisms.
Glue these maps and their inverses on the standard-open cover. For an arbitrary local
fraction b*s=a, the chart formula gives psi(b)*theta(s)=psi(a); multiplying by a
coefficient c gives the stated normalization. Local fraction descriptions extend this
identity to every open. No cancellation in the original rings or flatness is used.
(blueprint: lem-sfb-proj-scalar-extension-twist-existence). -/
theorem scalarExtension_twist_exists
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (ρA : R →+* 𝒜 0) (ρB : S →+* ℬ 0)
    (hρA : ∀ a : R, (ρA a : A) = algebraMap R A a)
    (hρB : ∀ b : S, (ρB b : B) = algebraMap S B b)
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (r : Proj ℬ ⟶ Proj 𝒜)
    (hpre : ∀ (n : ℕ) (f : A), f ∈ 𝒜 n → 0 < n →
      r ⁻¹ᵁ basicOpen 𝒜 f = basicOpen ℬ (ψ f))
    (hchart : ∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
      awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r =
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
          awayι 𝒜 f hf hn):
    ∃ θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j,
      IsScalarExtensionTwistComparison ψ r θ := by
  sorry

end AlgebraicGeometry.Proj
