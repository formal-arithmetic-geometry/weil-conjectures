/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
public import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!
# Étale proper base change for module coefficients

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/sk-thm-properbasechange-modules.md
(blueprint: det-properbasechange-modules).

## Main statements

* `properBaseChangeModules` identifies the module exchange map with the
  underlying abelian exchange map and gives the torsion proper-base-change
  consequence.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- For a proper morphism, forgetting coefficients identifies the derived exchange map
with the abelian exchange map.  If the cohomology sheaves of the forgotten complex are
 torsion, the module exchange map is an isomorphism.

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/sk-thm-properbasechange-modules.md, node
`det-properbasechange-modules` (blueprint: det-properbasechange-modules).

Proof:
1. Apply `exchange_forget_coefficients` to the chosen Cartesian square.  Its canonical
   edge comparisons give the displayed equality between the forgotten module exchange
   and the abelian exchange.
2. Exact forgetting identifies torsion cohomology of the module complex with torsion
   cohomology of its underlying abelian complex.  Apply the bounded-below proper base
   change theorem to the latter and use the equivalence clause of
   `exchange_forget_coefficients` to obtain invertibility of the module exchange.
-/
theorem properBaseChangeModules (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    [IsProper f]
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D+(moduleAbelianForget Λ Y').map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ≫
      (moduleAbelianDerivedExchangeTargetIso Λ g' f' K).hom =
      (moduleAbelianDerivedExchangeSourceIso Λ f g K).hom ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          (D+(moduleAbelianForget Λ X).obj K)) ∧
    ((∀ n : ℤ,
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
      ((D+(moduleAbelianForget Λ X)).obj K)).IsTorsion) →
      IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        sq.toCommSq).app K)) := by
  sorry

end AlgebraicGeometry.Etale
