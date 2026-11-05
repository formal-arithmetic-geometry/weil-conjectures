/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-!
# The projection formula for a bounded second argument

Let `Λ` be a finite ring, `g : Z ⟶ Y` a proper morphism and `j : U ⟶ Z` an open immersion. For
`K` in `Dᵇctf(U_proét, Λ)` and `L` a bounded complex of étale origin on `Y` (not necessarily of
finite Tor amplitude), the projection map `Rg_*(j_! K) ⊗ᴸ L ⟶ Rg_*(j_! K ⊗ᴸ Lg^* L)` is an
isomorphism. As in `AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_comparison`
this is the étale projection formula transported along `ν^*`; the boundedness of
`j_! K ⊗ᴸ Lg^* L` now comes from the finite Tor amplitude of `K` rather than of `L`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Coefficients

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end Coefficients

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end AlgebraicGeometry.ProEtale
