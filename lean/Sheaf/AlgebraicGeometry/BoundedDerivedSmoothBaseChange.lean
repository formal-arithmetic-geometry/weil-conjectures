/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
import Sheaf.AlgebraicGeometry.HypercohomologyConvergence
import Sheaf.AlgebraicGeometry.FiniteRangeComparison
import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
import Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility
import Sheaf.AlgebraicGeometry.HypercohomologyConvergenceStatement

/-!
# Bounded derived smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1437
(blueprint: sbc-thm-bounded-derived-smooth-base-change); Stacks Project, Tags 0EYU and 0F09.

The exchange is the canonical module-coefficient exchange on the unbounded derived
categories, with the square's vertical and horizontal roles exchanged.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Smooth pullback commutes with derived direct image of bounded constructible complexes
with the prescribed finite coefficients. The conclusion is in the ambient unbounded
module derived category; it imposes no boundedness or constructibility on either endpoint.
Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1437; Stacks Project,
Tags 0EYU, 0F09, 015J, 0D6J and 07A7
(blueprint: sbc-thm-bounded-derived-smooth-base-change).

Proof:
1. By `lem-kun-unbounded-abelian-exchange-comparison`, exact conservative derived
coefficient forgetting sends K to an abelian complex L with the same cohomological
bounds [a,b]. Each stalk element of H^q(L) is killed by N, since (N : Λ) = 0.
Its order d divides N, and d is invertible on S: writing N = dm, its inverse is m/N.
This uses `sbc-def-coefficient-conventions` and `def-weil-pbc-constructible-complexes`.
2. Apply `sbc-thm-smooth-base-change` to every H^q(L). Smoothness of f and the qcqs
hypotheses on g give isomorphisms of the degreewise exchange maps for p ≥ 0.
3. Rename the generic square (X₀,Y₀,X'₀,Y'₀;f₀,f'₀,g₀,g'₀) as (T,S,Y,X;g,h,f,e).
Use `lem-weil-pbc-truncation-couple-morphism` for the morphism of truncation couples
induced by the actual bounded-below exchange. Its E₂ arrows are those of step 2.
By `lemma-weil-pbc-hypercohomology-convergence`, both sequences lie in p ≥ 0, q ≥ a
and converge with finite filtrations in each total degree. For p < 0 both terms vanish.
4. Apply `sbc-lem-finite-range-comparison` to obtain invertibility of the bounded-below
abelian exchange. By `lem-sbc-abelian-derived-exchange-plus-compatibility`, the unbounded
abelian exchange is its bounded-below inclusion conjugated by the canonical endpoint
isomorphisms, and is therefore invertible. No upper bound on either output is used.
5. By `sbc-def-base-change-map` the map below is precisely the module exchange on this
renamed square. The canonical endpoint isomorphisms in
`lem-kun-unbounded-abelian-exchange-comparison` intertwine its forgotten arrow with the
abelian exchange of step 4. That forgotten arrow is thus invertible. Conservativity
of coefficient forgetting gives invertibility of the specified module exchange. -/
theorem isIso_derivedBaseChangeMap_of_boundedConstructible_of_smooth
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (sq : ChosenCartesianSquare h e f g) (N : ℕ)
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S)
    (K : DerivedCategoryModule Λ T) (hK : DerivedCategory.isBoundedConstructible Λ T K) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app K) := by
  sorry

end AlgebraicGeometry.Etale
