/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-!

# The derived comparison functor `D(ν^*)`

The comparison functor `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` of
`WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` is exact, so it induces a functor
`D(ν^*) : D(X_ét) ⥤ D(X_proét)` between the derived categories by applying it termwise to
complexes, with no derivation needed. It is Mathlib's `Functor.mapDerivedCategory`, whose
API is recorded in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedComparisonUpperStar`: the functor
  `D(ν^*) : D(X_ét) ⥤ D(X_proét)`.
- `AlgebraicGeometry.ProEtale.derivedComparisonUpperStarHomologyFunctorIso`: `D(ν^*)`
  commutes with the homology functors, `H^n ⋙ ν^* ≅ D(ν^*) ⋙ H^n`.
- `AlgebraicGeometry.ProEtale.derivedComparisonUpperStarPlus`: the restriction
  `D⁺(X_ét) ⥤ D⁺(X_proét)` of `D(ν^*)` to the bounded below derived categories.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

/-- The functor `D(ν^*) : D(X_ét) ⥤ D(X_proét)` induced on derived categories by the exact
comparison functor `ν^* = ProEtale.comparisonUpperStar`, applied termwise to complexes. -/
noncomputable def derivedComparisonUpperStar :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (comparisonUpperStar A X).mapDerivedCategory

/-- The functor `D(ν^*)` commutes with the homology functors: `H^n(ν^* K) ≅ ν^* H^n(K)`,
since `ν^*` is exact. -/
noncomputable def derivedComparisonUpperStarHomologyFunctorIso (n : ℤ) :
    _root_.DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n ⋙
        comparisonUpperStar A X ≅
      derivedComparisonUpperStar A X ⋙
        _root_.DerivedCategory.homologyFunctor (Sheaf (Scheme.ProEt.topology X) A) n :=
  (comparisonUpperStar A X).mapDerivedCategoryHomologyFunctorIso n

/-- The restriction `D⁺(X_ét) ⥤ D⁺(X_proét)` of `D(ν^*)` to the bounded below derived
categories. -/
noncomputable def derivedComparisonUpperStarPlus :
    _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) :=
  (comparisonUpperStar A X).mapDerivedCategoryPlus

end AlgebraicGeometry.ProEtale
