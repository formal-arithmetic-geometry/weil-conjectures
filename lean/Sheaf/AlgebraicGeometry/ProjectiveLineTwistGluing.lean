/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import Sheaf.AlgebraicGeometry.ProjectiveSpace.ProjectiveLineTwistData

/-!
# Gluing the two free modules defining a projective-line twist

Source: Weil conjectures blueprint, `lem-sc-p1-twist-exists`, proof, construction of
free rank-one modules and their transition maps; Stacks Project, Sheaves, Lemma 00AM.
(blueprint: lem-sc-p1-twist-gluing)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveLine

/-- The free modules on the two standard charts glue to a module with `TwistData`.
This statement asserts only existence of the module and its generators.

Source: Weil conjectures blueprint, `lem-sc-p1-twist-exists`, proof, first three
sentences (local free modules, transition map, cocycle, and gluing); Stacks Project,
Sheaves, Lemma 00AM.

Proof: On each standard open take the structure sheaf as a free rank-one module.
On the intersection use multiplication by `u₀₁ = (x₀/x₁)^d`, with inverse
multiplication by `u₀₁⁻¹`; on self-overlaps use identities. These maps commute
with restriction because restriction is a ring homomorphism. The two nontrivial
cocycle identities are multiplication by `u₀₁u₀₁⁻¹ = 1` and `u₀₁⁻¹u₀₁ = 1`;
the other identities involve an identity map. The standard opens cover the line.
Apply the existence clause of `glue_sheaves_of_modules` to obtain a sheaf `L`
and compatible isomorphisms `φᵢ : L.over Uᵢ ≅ 𝒪.over Uᵢ`. Define `gᵢ` as the
inverse image of `1` under `φᵢ` on `Uᵢ`. Naturality and linearity show that on
every `V ≤ Uᵢ`, multiplication by the restriction of `gᵢ` is exactly `φᵢ⁻¹`
on sections, hence is bijective. The compatibility equation
`φ₀ ≫ (multiplication by u₀₁) = φ₁` on the intersection sends the restriction
of `g₀` to `u₀₁`; applying `φ₁⁻¹` gives `g₀ = u₀₁ • g₁`. These are precisely
all five fields of `TwistData`, for positive, zero, and negative degrees alike.
(blueprint: lem-sc-p1-twist-gluing). -/
theorem exists_twistData (k : Type u) [Field k] (d : ℤ) :
    ∃ L : (ProjectiveLine (Spec (.of k))).Modules,
      Nonempty (TwistData (Spec (.of k)) d L) := by
  exact ⟨ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d,
    nonempty_twistData_projectiveSpace k d⟩

end AlgebraicGeometry.ProjectiveLine
