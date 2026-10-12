/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-!
# Field-valued points factor through closed immersions

Source: literature/stacks-project/schemes.tex, Schemes, Lemma Tag 0356
(applied to `Spec K`), with Definition Tag 01HK and Lemma Tag 01L7
(blueprint: lem-weil-pbc-field-point-factors-through-closed-immersion).
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/--
(blueprint: lem-weil-pbc-field-point-factors-through-closed-immersion)
Let `i : Z ⟶ X` be a closed immersion of schemes, let `K` be a field,
and let `s : Spec K ⟶ X` have image point `i z`. Then there is exactly one
morphism `s' : Spec K ⟶ Z` with `s' ≫ i = s`, and its unique point maps to `z`.
Source: Stacks Project, Schemes, Tag 0356, Definition Tag 01HK, Lemma Tag 01L7.

Proof: Write `x = s(ξ) = i(z)`. By `lem-weil-pbc-morphism-from-spec-field`,
`s = j_x ∘ Spec(φ)` for a unique residue-field map `φ : κ(x) → K`.
The map `r : κ(x) → κ(z)` induced by `i` is an isomorphism by
`lem-weil-pbc-closed-immersion-residue-field-iso`. Set `ψ = φ ∘ r⁻¹` and
`s' = j_z ∘ Spec(ψ)`. Naturality (`lem-weil-pbc-residue-field-point-naturality`)
gives `i ∘ j_z = j_x ∘ Spec(r)`. Contravariant functoriality of Spec
(`def-weil-affine-spectrum`) now gives `i ∘ s' = s`, and the canonical point
morphism sends the unique point to `z`.
For any lift `t`, injectivity on points of the closed immersion
(`def-weil-closed-immersion`) gives `t(ξ) = z`. Write `t = j_z ∘ Spec(ψ_t)`
using `lem-weil-pbc-morphism-from-spec-field`. Naturality and injectivity of that
point-and-field-map correspondence give `ψ_t ∘ r = φ`; hence `ψ_t = ψ` and `t = s'`.
-/
theorem field_point_factors_through_closed_immersion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ X) (z : Z)
    (h : s.base (default : Spec (.of K)) = i.base z) :
    (∃! s' : Spec (.of K) ⟶ Z, s' ≫ i = s) ∧
      ∀ s' : Spec (.of K) ⟶ Z, s' ≫ i = s → s'.base (default : Spec (.of K)) = z := by
  sorry

end AlgebraicGeometry
