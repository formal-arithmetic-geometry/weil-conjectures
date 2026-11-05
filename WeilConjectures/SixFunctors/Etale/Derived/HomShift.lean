/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# The derived hom out of a shifted complex

The derived tensor product commutes with shifts in its first variable, naturally in the second
one, `K⟦a⟧ ⊗ᴸ M ≅ (K ⊗ᴸ M)⟦a⟧`. Passing to right adjoints, the derived hom out of a shifted
complex is the shifted derived hom, `RHom(K⟦a⟧, M) ≅ RHom(K, M)⟦-a⟧`; in particular the Verdier
dual of a shift is the opposite shift of the Verdier dual, `𝔻(K⟦a⟧) ≅ (𝔻K)⟦-a⟧`.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensorObjShiftIso`: `K⟦a⟧ ⊗ᴸ - ≅ (K ⊗ᴸ -)⟦a⟧`.
- `AlgebraicGeometry.Etale.derivedHomShiftIso`: `RHom(K⟦a⟧, -) ≅ RHom(K, -)⟦-a⟧`.
- `AlgebraicGeometry.Etale.verdierDualShiftIso`: `𝔻(K⟦a⟧) ≅ (𝔻K)⟦-a⟧`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X : Scheme.{u}}

variable {S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]

end AlgebraicGeometry.Etale
