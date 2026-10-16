/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

import Sheaf.CategoryTheory.DerivedCoupleExact
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Finite-tail limiting subobjects

Source: Stacks Project, Tag 011T, exact-couple cycle and boundary formulas.
(blueprint: lem-sp-finite-cocone-limit-cycles)
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- An upper zero tail identifies the limiting cycles with the initial g image.
Source: Stacks Project, Tag 011T, formula for cycles; Tag 012W, upper-tail argument.
(blueprint: lem-sp-finite-cocone-limit-cycles).

Proof: Use the recursive image and mono inclusion families of pageCouple_image_prefix.
Induct on r to show that the finite cycle projection followed by page f and
its D inclusion equals the finite cycle inclusion followed by the original f.
The base is projection_zero. For the successor use projection_succ,
DerivedMaps.f_comm, cycleLift_comm and the preceding induction equation.
Choose r beyond the upper bound on total degree p+q+1 (and beyond a regularity
bound). The source of the original incoming r-fold alpha map at (p+2,q-1)
is zero. Its image, hence the image of the mono D inclusion, is zero; the
inclusion itself is zero. The projection equation now makes original f vanish
on Z_r. Since L.Z is below Z_r by its GLB property, original f vanishes on L.Z.
Exactness identifies ker f with image initialG, using the canonical type-zero
transport and naturality of f. Thus L.Z is contained in image initialG.
Conversely, g_factors_limitCycles places image initialG below L.Z. The two
inequalities prove equality without a general finite-cycle formula. -/
theorem finiteCocone_limitCycles
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (L : X.LimitSubobjects) (hreg : X.IsRegular)
    (hzero : ∀ n : ℤ, ∃ b : ℤ, ∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P)))
    (p q : ℤ) : L.Z p q = imageSubobject (X.initialG p q) := by
  sorry

end CategoryTheory.BigradedExactCouple
