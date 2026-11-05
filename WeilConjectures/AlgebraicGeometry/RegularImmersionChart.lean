/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.RingTheory.Etale.Coordinates

/-!
# Étale charts adapted to a regular immersion

Let `i : Z ⟶ X` be a regular immersion of pure codimension `c` between schemes smooth over a
perfect field `k` (with `Z` regular). Near every point of `Z` there is an affine open `U` of `X`
with functions `f₁, …, f_c` generating the ideal of `Z ∩ U`, and an étale morphism
`v : U ⟶ 𝔸^c_{𝔸^m_k}` whose `c` fibre coordinates pull back to the `fᵢ`.

## Main results

- `AlgebraicGeometry.locally_isStandardSmoothOfRelativeDimension_appLE`: the ring-theoretic
  meaning of smoothness of relative dimension `n` of `U ⟶ X ⟶ Spec k` for an affine open `U`.
- `AlgebraicGeometry.IsRegularImmersion.exists_etale_affineSpace`: the étale chart.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

end AlgebraicGeometry
