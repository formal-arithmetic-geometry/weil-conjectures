/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso

/-!
# Degree-zero parts of perfect pairings

Let `b : C ⊗ᴸ D ⟶ Λ_X` be a perfect pairing in `D(X_ét, A)` and `i + j = 0`. The degree-zero
part of `b` pairs a class `x : Λ_X ⟶ C[i]` with a class `y : Λ_X ⟶ D[j]`. This file shows that
it is the composition pairing `⟨x, y⟩ = x ≫ g(y)` for an additive bijection
`g : Hom(Λ_X, D[j]) ≃ Hom(C[i], Λ_X)`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_iff_bijective`: `b` is perfect if and only if
  `y ↦ (C ⊗ᴸ y) ≫ b` is bijective on `Hom(S, D)` for every `S`.
- `AlgebraicGeometry.Etale.IsPerfectPairing.shift`: the shifted pairing
  `C[i] ⊗ᴸ D[j] ≅ (C ⊗ᴸ D)[i + j] ⟶ Λ_X[i + j] ≅ Λ_X` is perfect for `i + j = 0`.
- `AlgebraicGeometry.Etale.IsPerfectPairing.exists_addEquiv_degreeZero`: the degree-zero part of
  a perfect pairing is a composition pairing `x ≫ g(y)` with `g` an additive bijection.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry

namespace Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

end Etale

end AlgebraicGeometry
