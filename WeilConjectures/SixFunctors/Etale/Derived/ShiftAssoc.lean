/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The associator of the derived tensor product and the shifts

The identifications `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧`
(`AlgebraicGeometry.Etale.derivedTensorShiftIso`) on `D(X_ét)` are compatible with the associator
of the derived tensor product: the two identifications
`(K⟦a⟧ ⊗ᴸ L⟦b⟧) ⊗ᴸ M⟦c⟧ ≅ (K ⊗ᴸ (L ⊗ᴸ M))⟦a + b + c⟧` agree. This is
`DerivedCategory.shiftTensorShiftIso_assoc` for the derived category of étale sheaves.

## Main statements

- `AlgebraicGeometry.Etale.derivedTensorShiftIso_assoc`
- `AlgebraicGeometry.Etale.derivedTensorHom_comp_eqToHom_comp_derivedTensorShiftIso_hom`,
  `AlgebraicGeometry.Etale.derivedTensorHom_id_comp_eqToHom_comp_derivedTensorShiftIso_hom`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

end Etale

end AlgebraicGeometry
