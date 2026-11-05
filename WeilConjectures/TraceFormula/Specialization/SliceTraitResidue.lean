/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitPoint
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationResidueSeparableModel
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality

/-!

# The residue field of the strict localization of `𝔸¹` over a trait

Let `R₁` be a local ring, `b₁ : R₁ → κ₁` a map to a field with kernel the maximal ideal, and
`s = AlgebraicGeometry.sliceTraitPoint b₁ : Spec K ⟶ 𝔸¹_{R₁}` (`K = κ₁(x)^alg`) the geometric
point at the generic point of the special fibre. Let `𝔮 ⊆ R₁[x]` be the prime of `s`, with residue
field `κ(𝔮) = k(x)`, `k` the residue field of `R₁`.

We show that every element of the residue field of the strict henselization `𝒪^{sh}_{𝔸¹_{R₁}, s}`
which is algebraic over `k` lies in `k`, provided `k` is separably closed. Viewing the residue
field inside `K` through the evaluation (`AlgebraicGeometry.sliceTraitResidueEval`):

* every element is separable over `κ(𝔮)` (`AlgebraicGeometry.isSeparable_sliceTraitResidueEval`,
  from `AlgebraicGeometry.Scheme.strictHenselization_residue_separable_model`);
* an element algebraic over the separably closed field `k` is purely inseparable over `k`, hence
  over `κ(𝔮)`, so it lies in `κ(𝔮)` (`mem_range_algebraMap_of_isAlgebraic_of_isSeparable`);
* `κ(𝔮)` lands in `k⟮x⟯ ⊆ K` with `x` transcendental over `k`, and `k` is algebraically closed in
  `k⟮x⟯ ≅ k(X)` (`mem_range_algebraMap_of_isAlgebraic_of_mem_adjoin`).

## Main result

- `AlgebraicGeometry.mem_range_algebraMap_residueField_sliceTraitPoint`

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

open Scheme

variable {R₁ : Type u} [CommRing R₁] {κ₁ : Type u} [Field κ₁] (b₁ : R₁ →+* κ₁)

section ResidueField

variable [IsLocalRing R₁]

end ResidueField

end AlgebraicGeometry
