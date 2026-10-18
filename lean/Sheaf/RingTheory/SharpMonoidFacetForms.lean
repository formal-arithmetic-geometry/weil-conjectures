/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Primitive nonnegative facet forms of a monoid

Source: ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70, for the monoid
models; the facet forms are those of the item lem-trf-complete-toric-boundary-class-injectivity
(blueprint: def-trf-sharp-monoid-facet-forms).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- The primitive nonnegative facet forms of `P`: surjective homomorphisms
`ν : P^gp → ℤ`, nonnegative on `P`, whose zero set in `P` spans a rational subspace of
codimension one, so that `σ ∩ ker ν` is a facet of the cone `σ` of `P`.
Source: ILO VI 1.6(i)--(ii), p. 70, monoid models; facet forms as in the item
lem-trf-complete-toric-boundary-class-injectivity
(blueprint: def-trf-sharp-monoid-facet-forms). -/
def MonoidFacetForm (P : Type u) [AddCommMonoid P] :=
  {ν : GrothendieckAddGroup P →+ ℤ // Function.Surjective ν ∧
    (∀ q : P, 0 ≤ ν (GrothendieckAddGroup.of q)) ∧
    Module.finrank ℚ (ℚ ⊗[ℤ]
      AddSubgroup.closure {g : GrothendieckAddGroup P |
        ∃ q : P, ν (GrothendieckAddGroup.of q) = 0 ∧
          g = GrothendieckAddGroup.of q}) + 1 =
      Module.finrank ℚ (ℚ ⊗[ℤ] GrothendieckAddGroup P)}

/-- The facet vector `g ↦ (ν_F(g))_F` for an enumeration of the facet forms.
Source: ILO VI 1.6(i)--(ii), p. 70; the map `ν` of the item
lem-trf-complete-toric-boundary-class-injectivity
(blueprint: def-trf-sharp-monoid-facet-forms). -/
def monoidFacetVector {P : Type u} [AddCommMonoid P] {F : Type v}
    (facets : F ≃ MonoidFacetForm P) :
    GrothendieckAddGroup P →+ (F → ℤ) where
  toFun g i := (facets i).1 g
  map_zero' := funext fun i ↦ (facets i).1.map_zero
  map_add' g h := funext fun i ↦ (facets i).1.map_add g h

end Algebra
