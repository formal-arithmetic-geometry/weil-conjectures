/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.LowerShriek.Defs

/-!

# The derived adjunction `j_! ⊣ j^*` along an open immersion, on module objects

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenImmersionLowerShriek`, for
the coefficient ring objects `ℚ̄_ℓ,X` of `WeilConjectures.CategoryTheory.RingObjects.EllAdic`.

For an open immersion `j : U ⟶ X` both halves of the adjunction
`ProEtale.PadicAlgClRing.openImmersionLowerShriekUpperStarAdjunction` on module objects are
*exact*: the extension by zero `j_!` by
`ProEtale.PadicAlgClRing.preservesHomology_openImmersionLowerShriek`, and the pullback `j^*`
by `ProEtale.PadicAlgClRing.preservesHomology_upperStar_of_isOpenImmersion`, since the
coefficient morphism `α_j : j^* ℚ̄_ℓ,X ⟶ ℚ̄_ℓ,U` is an isomorphism. So each of them induces a
functor on derived categories by applying it levelwise, and the two levelwise functors are
again adjoint.

As in the finite-coefficient case the adjunction is obtained where the derived formalism
provides it, namely between the *total* derived functors
(`Adjunction.derivedAdjunction`), and exactness then identifies each total derived functor
with the corresponding levelwise functor; both steps are the general
`Adjunction.mapDerivedCategoryAdjunction` and `Adjunction.mapDerivedCategoryPlusAdjunction` of
`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`. In particular the derived pullback
`L((j)^*⟦ℚ̄_ℓ⟧)` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.UpperLowerStar` is,
for an open immersion, the levelwise functor `D((j)^*⟦ℚ̄_ℓ⟧)`
(`ProEtale.PadicAlgClRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion`).

## Main results

- `ProEtale.PadicAlgClRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion`:
  `L((j)^*⟦ℚ̄_ℓ⟧) ≅ D((j)^*⟦ℚ̄_ℓ⟧)` for an open immersion `j`.

- `ProEtale.PadicAlgClRing.derivedOpenImmersionLowerShriekUpperStarAdjunction` and
  `ProEtale.PadicAlgClRing.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus`: the
  derived adjunctions `D((j)_!open⟦ℚ̄_ℓ⟧) ⊣ D((j)^*⟦ℚ̄_ℓ⟧)` and
  `D+((j)_!open⟦ℚ̄_ℓ⟧) ⊣ D+((j)^*⟦ℚ̄_ℓ⟧)`.

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j : U ⟶ X`, the pullback `j^*` on module objects is exact, so its
total left derived functor `L((j)^*⟦ℚ̄_ℓ⟧)`, computed via K-flat resolutions, is canonically
isomorphic to the levelwise functor `D((j)^*⟦ℚ̄_ℓ⟧)`. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion :
    L((j)^*⟦ℚ̄_ℓ⟧) ≅ D((j)^*⟦ℚ̄_ℓ⟧) :=
  (j)^*⟦ℚ̄_ℓ⟧.leftDerivedFunctorIsoMapDerivedCategory

/-- The derived adjunction `j_! ⊣ j^*` along an open immersion `j : U ⟶ X` on the unbounded
derived categories of module objects over `ℚ̄_ℓ`: since both `j_!` and `j^*` are exact on
module objects, their total derived functors are the levelwise functors, and the adjunction
between the total left derived functor of `j_!` and the total right derived functor of `j^*`
becomes an adjunction between the levelwise functors. -/
noncomputable def derivedOpenImmersionLowerShriekUpperStarAdjunction :
    D((j)_!open⟦ℚ̄_ℓ⟧) ⊣ D((j)^*⟦ℚ̄_ℓ⟧) :=
  (openImmersionLowerShriekUpperStarAdjunction ℓ j).mapDerivedCategoryAdjunction

/-- The bounded below version of
`ProEtale.PadicAlgClRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`: the derived
adjunction `j_! ⊣ j^*` along an open immersion on the bounded below derived categories of
module objects, obtained by restricting the unbounded one along the fully faithful inclusions,
which is legitimate since the exact functors `j_!` and `j^*` preserve bounded below objects. -/
noncomputable def derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus :
    D+((j)_!open⟦ℚ̄_ℓ⟧) ⊣ D+((j)^*⟦ℚ̄_ℓ⟧) :=
  (openImmersionLowerShriekUpperStarAdjunction ℓ j).mapDerivedCategoryPlusAdjunction

instance : D((j)_!open⟦ℚ̄_ℓ⟧).IsLeftAdjoint :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ j).isLeftAdjoint

instance : D((j)^*⟦ℚ̄_ℓ⟧).IsRightAdjoint :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ j).isRightAdjoint

end AlgebraicGeometry.ProEtale.PadicAlgClRing
