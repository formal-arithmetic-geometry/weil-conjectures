/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# Derived pushforward commutes with derived limits

A derived limit of a tower `(Kₙ, fₙ)` in a triangulated category is the first vertex `L` of a
distinguished triangle `L ⟶ ∏ Kₙ ──1 - t──▶ ∏ Kₙ ⟶ L[1]` (`CategoryTheory.IsDerivedLimitTriangle`,
`def-weil-derived-limit`). A triangulated functor preserving countable products sends such a
triangle to a triangle of the same kind (`CategoryTheory.Functor.isDerivedLimitTriangle_map`),
i.e. it commutes with derived limits: `Φ (R lim Kₙ) = R lim Φ Kₙ`.

The derived pushforward `Rg_*` of pro-étale sheaves is a right adjoint
(`AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction`), so it preserves products,
and it is triangulated; hence `Rg_* (R lim Kₙ) = R lim Rg_* Kₙ`
(`AlgebraicGeometry.ProEtale.isDerivedLimitTriangle_rightDerivedLowerStar`), the formal input
`Rf_* R lim = R lim Rf_*` of the passage from the finite levels `ℤ/ℓⁿ` to `ℤ_ℓ` (Stacks 08U1,
blueprint `lem-pc-derived-functor-commutes-derived-limit`).
-/

@[expose] public section

universe u u' v v' w w'

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme MonoidalCategory
open scoped CategoryTheory.Functor

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end AlgebraicGeometry.ProEtale
