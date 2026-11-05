/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.RepresentationTheory.Filtration

/-!
# The exterior powers of a filtered representation

Let `U ⊆ V` be a subspace. The `n`-th exterior power `⋀ⁿ V` is filtered by the subspaces
`F_j = span {v₁ ∧ ⋯ ∧ vₙ | at least j of the vᵢ lie in U}`
(`exteriorPower.countSpan`), with `F_0 = ⋀ⁿ V` and `F_{n+1} = 0`, and the graded pieces are

$$
F_j / F_{j+1} \cong \textstyle\bigwedge^j U \otimes \bigwedge^{n-j} (V / U),
$$

via `u₁ ∧ ⋯ ∧ u_j ⊗ x̄₁ ∧ ⋯ ∧ x̄_l ↦ u₁ ∧ ⋯ ∧ u_j ∧ s(x̄₁) ∧ ⋯ ∧ s(x̄_l)` for a linear
section `s` of `V → V / U`. When `U` is a subrepresentation, the `F_j` are
subrepresentations and these isomorphisms are equivariant: changing the section changes the
image by an element of `F_{j+1}`.

As a consequence, the exterior powers of a representation and of its semisimplification have the
same constituents: the graded pieces of a filtration of `V` determine the constituents of `⋀ⁿ V`.

## Main definitions

- `exteriorPower.countSpan`: the filtration `F_j` of `⋀ⁿ V`.
- `exteriorPower.wedge`: the product `⋀ʲ V × ⋀ˡ V → ⋀ʲ⁺ˡ V`.
- `Subrepresentation.exteriorPowerFiltration`: the filtration `F_j` for a subrepresentation.

## Main results

- `exteriorPower.toGraded_bijective`: `⋀ʲ U ⊗ ⋀ⁿ⁻ʲ (V / U) ≃ F_j / F_{j+1}`.
- `Subrepresentation.exteriorPowerGradedEquiv`: the same, equivariantly.
- `Representation.ConstituentsLE.exteriorPower_of_chain`: the constituents of `⋀ⁿ` of a filtered
  representation only depend on the graded pieces.
- `Representation.CompositionSeries.constituentsLE_exteriorPower_semisimplification` and its primed
  version: `⋀ⁿ V` and `⋀ⁿ V^ss` have the same constituents.

## Blueprint

- `lem-mg-filtered-exterior-power`, `lem-mg-filtration-refinement`: the exterior power of a
  filtered representation, through its constituents. The full filtration with graded pieces
  `⨂ᵢ ⋀^{nᵢ} A_i` is in `WeilConjectures.RepresentationTheory.ExteriorPowerFiltration`.
-/

@[expose] public section

open TensorProduct

namespace exteriorPower

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

variable (P : Submodule k V) (n : ℕ)

/-! ### The graded pieces -/

section Graded

variable {P} (s : V ⧸ P →ₗ[k] V)

end Graded

end exteriorPower

/-! ### The filtration of the exterior power of a representation -/

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

variable (P : Subrepresentation ρ) (n : ℕ)

end Subrepresentation

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

end Subrepresentation

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]

end Representation

/-! ### The constituents of the exterior powers of a filtered representation -/

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
  {V V' V₁ V₂ : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  {ρ : Representation k W V} {σ : Representation k W V'}
  {ρ₁ : Representation k W V₁} {σ₁ : Representation k W V₂}

namespace ConstituentsLE

variable {V'' : Type*} [AddCommGroup V''] [Module k V''] {τ : Representation k W V''}

end ConstituentsLE

end Representation

namespace Representation

open DirectSum

variable {k : Type*} [Field k] {W : Type*} [Group W] {t : ℕ} {V : Fin t → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] (ρs : ∀ i, Representation k W (V i))

end Representation

namespace Representation.CompositionSeries

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {ρ : Representation k W V} (s : ρ.CompositionSeries)

end Representation.CompositionSeries
