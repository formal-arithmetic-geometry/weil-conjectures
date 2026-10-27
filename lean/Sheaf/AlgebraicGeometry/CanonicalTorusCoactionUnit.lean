/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B8
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# The unit law for canonical chart coactions

Source: ILO VIII 3.2.4, p.103, and the chartwise gluing argument in
Step 6 of lem-trf-lattice-torus-coordinates-action.
(blueprint: lem-trf-canonical-torus-coaction-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.Monoscheme

/-- Every morphism over k with the specified monomial chart coactions is unital.

Source: ILO VIII 3.2.4, p.103; Step 6 of the lattice torus argument.
(blueprint: lem-trf-canonical-torus-coaction-unit).
Proof: the component chart images cover componentOpen by its defining union.
On a chart with monoid P, the identity of Spec k[L] is the spectrum of the
counit, which sends every e^l to 1. Composing the chart coaction
 e^p ↦ e^deg(p) tensor e^p with this counit therefore sends e^p to e^p.
Both maps are k-algebra homomorphisms, so equality on these monomials implies
 equality on all finite sums. The affine fibre-product comparison identifies
this equation with the unit diagram on the chart. The assumed canonical
coaction formula identifies that local composite with the restriction of a.
The component charts cover X, and their products with the terminal k-scheme
cover the source of the unit diagram. Equality of scheme morphisms can be
checked on this open cover. This gives the asserted equality in Over Spec k,
whose forgetful functor is faithful. The argument needs no connectedness or
positive-rank assumption. -/
theorem canonicalTorusCoaction_unit (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M)
    (a : ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k))) ⊗
        Over.mk (componentToBase k C) ⟶ Over.mk (componentToBase k C))
    (ha : IsCanonicalTorusAction k C a.left) :
    (η[((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k)))] ▷
      Over.mk (componentToBase k C)) ≫ a =
        (λ_ (Over.mk (componentToBase k C))).hom := by sorry

end AlgebraicGeometry.Monoscheme
