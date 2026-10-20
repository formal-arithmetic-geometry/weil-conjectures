/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekCompactificationBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek

/-!
# The base change isomorphism of the extension by zero as a mate

Let `j : U ⟶ Z` be an open immersion. On the unbounded derived categories of pro-étale sheaves,
the extension by zero `j_!` is left adjoint to the derived pullback `Lj^*`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction`).

For a cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, the mate of the
base change isomorphism `L(g'')^* j_! ≅ j'_! Lg'^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso`) along
these adjunctions is the square isomorphism `Lj^* Lg'^* ≅ L(g'')^* Lj'^*` of derived pullbacks.
This is an input for the compatibility of the compact-support exchange maps with the change of
coefficients (blueprint `sk-p-trace-coeff`).

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction`:
  the adjunction `j_! ⊣ Lj^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Adjunction

variable {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]

/-- The adjunction `j_! ⊣ Lj^*` between the extension by zero along an open immersion `j` and the
derived pullback on the unbounded derived categories of pro-étale sheaves: the adjunction
`D(j_!) ⊣ D(j^*)` (`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction`)
transported along `Lj^* ≅ D(j^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction :
    D((j)_!open[A]) ⊣ L((j)^*[A]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory A j).symm

end Adjunction

section BaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The mate of the base change isomorphism `L(g'')^* j_! ≅ j'_! Lg'^*` of the extension by zero
along the adjunctions `j_! ⊣ Lj^*` and `j'_! ⊣ Lj'^*` is the square isomorphism
`Lj^* Lg'^* ≅ L(g'')^* Lj'^*` of derived pullbacks. -/
theorem mateEquiv_leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_inv
    (hsq : IsPullback g' j' j g'') :
    mateEquiv (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j)
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j')
        (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso A hsq).inv =
      (leftDerivedUpperStarSquareIso A hsq.toCommSq).inv := by
  sorry

end BaseChange

end AlgebraicGeometry.ProEtale
