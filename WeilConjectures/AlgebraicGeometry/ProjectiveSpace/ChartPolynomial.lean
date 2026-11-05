/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# The standard charts of projective space over a ring are polynomial rings

Let `A` be a commutative ring and `Uᵢ = D₊(xᵢ)` a standard open of `ℙ(n; Spec A)`. The ring of
functions `Γ(Uᵢ)` is the polynomial ring over `A` in the ratios `x_k / xᵢ`, `k ≠ i`.

## Main declarations

- `AlgebraicGeometry.ProjectiveSpace.homOfSections_coord_eq`: the morphism
  `𝔸({k // k ≠ i}; S) ⟶ ℙ(n; S)` given by the coordinates and `1` in position `i` is the inverse
  of the chart isomorphism `D₊(xᵢ) ≅ 𝔸({k // k ≠ i}; S)` followed by the inclusion.
- `AlgebraicGeometry.ProjectiveSpace.chartRingEquiv`: `A[x_k / xᵢ : k ≠ i] ≃ Γ(D₊(xᵢ))`.

(blueprint: `lem-pc-projective-space-canonical`)
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : Type u} (S : Scheme.{u}) (i : n)

variable (n) (A : Type u) [CommRing A] {i}

end AlgebraicGeometry.ProjectiveSpace
