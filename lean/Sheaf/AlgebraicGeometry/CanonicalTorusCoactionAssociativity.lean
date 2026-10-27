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
# The associativity law for canonical chart coactions

Source: ILO VIII 3.2.4, p.103, and the chartwise gluing argument in
Step 6 of lem-trf-lattice-torus-coordinates-action.
(blueprint: lem-trf-canonical-torus-coaction-associativity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.Monoscheme

/-- Every morphism over k with the specified monomial chart coactions is associative.

Source: ILO VIII 3.2.4, p.103; Step 6 of the lattice torus argument.
(blueprint: lem-trf-canonical-torus-coaction-associativity).
Proof: the component charts cover X by the defining union for componentOpen.
Their products with two copies of T cover T times T times X by base change
of open covers. On a chart P, the assumed formula for a factors its restriction
through that same chart. Thus both iterated actions on this product chart
are the spectra of the iterated coaction. The first composite applies the
torus comultiplication to the degree factor, and sends e^p to
 e^deg(p) tensor e^deg(p) tensor e^p. The other composite applies the chart
coaction to the second factor and gives the same tensor. Equality extends
from monomials to all finite sums by k-linearity. The associator of tensor
products corresponds under the affine spectrum comparison to the associator
of fibre products, so this is exactly the displayed local associativity
 equation. Equality of morphisms on the product chart cover proves it globally.
The faithful forgetful functor from Over Spec k then gives the displayed
 equality. No connectedness, separatedness or positive-rank assumption is used. -/
theorem canonicalTorusCoaction_associativity (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M)
    (a : ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k))) ⊗
        Over.mk (componentToBase k C) ⟶ Over.mk (componentToBase k C))
    (ha : IsCanonicalTorusAction k C a.left) :
    (μ[((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k)))] ▷
      Over.mk (componentToBase k C)) ≫ a =
        (α_ ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k)))
          ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k)))
          (Over.mk (componentToBase k C))).hom ≫
            ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k))) ◁ a ≫ a := by
  sorry

end AlgebraicGeometry.Monoscheme
