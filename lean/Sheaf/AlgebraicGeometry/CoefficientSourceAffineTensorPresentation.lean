/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Tensor presentation of associated-module coefficient sections

Source: Stacks Project, Tags 01I9 and 01IA.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Sections on an affine open of the pullback of an associated module have a
unit-compatible tensor presentation. This assertion involves no comparison morphism.
Source: Stacks Project, Tags 01I9 and 01IA, affine pullback of modules.
(blueprint: lem-pc-coefficient-source-affine-tensor-presentation).

Proof: Compose g with S.toSpecGamma and restrict to the affine scheme B. Pullback
composition is the unique isomorphism of left adjoints compatible with their units.
The affine pullback section formula for this composite identifies the sections with
R tensor_A N, where A = Gamma(S,O) and R = Gamma(B,O). The ring map A -> R is
g.appLE top B: the canonical GammaSpecIso cancels the chart's scalar map. The unit
of the tilde/Gamma adjunction sends s to tilde.toOpen N top s. Compatibility of
composite pullback units therefore sends the displayed coefficientGenerator,
restricted to B, to 1 tensor s. Swap tensor factors if the section formula is
written N tensor_A R. The formula and equivalence are also valid for B empty
or N zero, since both sides then have the corresponding zero module. -/
theorem exists_coefficientSource_affine_tensor_presentation
    {S S' : Scheme.{u}} (g : S' ⟶ S) (N : ModuleCat.{u} Γ(S, ⊤))
    (B : S'.Opens) (hB : IsAffineOpen B) :
    letI : Algebra Γ(S, ⊤) Γ(S', B) := (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let P := (pullback g).obj ((pullback S.toSpecΓ).obj (tilde N))
    ∃ e : Γ(P, B) ≃ₗ[Γ(S', B)] (Γ(S', B) ⊗[Γ(S, ⊤)] N),
      ∀ s : N, e (P.presheaf.map (homOfLE le_top).op
        (coefficientGenerator g N s)) = (1 : Γ(S', B)) ⊗ₜ[Γ(S, ⊤)] s := by sorry

end
end AlgebraicGeometry.Scheme.Modules
