/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-!

# The derived comparison functors

The comparison functor `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` of
`WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` is exact, so it induces functors
`D(ν^*) : D(X_ét) ⥤ D(X_proét)` and `D⁺(ν^*) : D⁺(X_ét) ⥤ D⁺(X_proét)` by applying it termwise
to complexes. As for the pullback in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`,
these functors and the right derived functor `R⁺ν_*` are not given definitions of their own:
they are the generic constructions `D(-)`, `D+(-)` and `R+(-)` of the folder
`WeilConjectures.CategoryTheory.DerivedCategory`, recorded below as `example`s.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus`: the adjunction
  `D+(ν^*(X)[A]) ⊣ R+(ν_*(X)[A])` between the bounded below derived categories of étale and
  pro-étale sheaves.

-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

/-- The functor `D(ν^*) : D(X_ét) ⥤ D(X_proét)` induced by the exact functor `ν^*`. -/
noncomputable example :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  D(ν^*(X)[A])

/-- The functor `D⁺(ν^*) : D⁺(X_ét) ⥤ D⁺(X_proét)` induced by the exact functor `ν^*`. -/
noncomputable example :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) :=
  D+(ν^*(X)[A])

/-- The right derived functor `R⁺ν_* : D⁺(X_proét) ⥤ D⁺(X_ét)` of the restriction `ν_*`. -/
noncomputable example :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
  R+(ν_*(X)[A])

section Adjunction

/- The closed symmetric preadditive monoidal structure and the functorial flat resolutions on
the coefficient category, as in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
the adjunction is obtained from the unbounded derived adjunction, whose left adjoint is
derived via K-flat resolutions of étale sheaves. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The adjunction `D⁺(ν^*) ⊣ R⁺ν_*` between the bounded below derived categories of étale and
pro-étale sheaves, induced by the adjunction `ν^* ⊣ ν_*`. -/
noncomputable def derivedComparisonAdjunctionPlus : D+(ν^*(X)[A]) ⊣ R+(ν_*(X)[A]) :=
  (comparisonAdjunction A X).derivedAdjunctionPlus

end Adjunction

end AlgebraicGeometry.ProEtale
