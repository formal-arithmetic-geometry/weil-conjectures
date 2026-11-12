/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Orientation

/-!
# The dualizing complex of a smooth variety

Let `X` be smooth and separated of pure dimension `d` over a field `k`, with structure morphism
`a_X : X ⟶ Spec k`, and let `Λ` be a finite coefficient ring whose exponent is invertible on `X`.
Smooth purity (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`) identifies
the dualizing complex `ω_X = Ra_X^! Λ` with the shifted Tate twist `Λ_X(d)[2d]`. This is the
first isomorphism of blueprint `theorem-poincare-duality`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_tateObject_shift`:
  `ω_X ≅ Λ_X(d)[2d]`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Etale

/-- Blueprint `theorem-poincare-duality--1`: for `X` smooth and separated of pure dimension `d`
over a field `k` (in the blueprint `k` is algebraically closed) and a finite coefficient ring
`Λ` whose exponent is invertible on `X`, smooth purity gives

`ω_X = Ra_X^! Λ ≅ Λ_X(d)[2d]`.

It is the orientation of `a_X` constructed by smooth purity
(`AlgebraicGeometry.Etale.Orientation.nonempty`), read at the structure morphism
(`AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`). -/
theorem nonempty_iso_dualizingComplex_tateObject_shift (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] {k : Type u} [Field k]
    {X : Scheme.{u}} {d : ℕ} (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [SmoothOfRelativeDimension d aX] [HasCompactification aX] [HasInvertibleExponent Λ X] :
    Nonempty (dualizingComplex Λ aX ≅ (tateObject Λ X d)⟦(2 * d : ℤ)⟧) := by
  obtain ⟨o⟩ := Orientation.nonempty (Λ := Λ) (d := d) aX (𝟙 (Spec (.of k)))
  exact o.nonempty_iso_dualizingComplex

end Etale

end AlgebraicGeometry
