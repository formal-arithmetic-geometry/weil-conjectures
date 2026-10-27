/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.FiniteProperProductMaps
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.SmoothPurity.OrdinaryDerivedCompositeTranspose

/-! # The intrinsic finite compositor is the canonical adjunction mate

Source: Stacks Project, Tags 07A6, 0D6D and 0D6E, and the normalization step of
`lem-pur-finite-proper-product-transpose`.
(blueprint: lem-pur-finite-proper-compositor-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.FiniteProperProduct

/-- The specified transported direct-image compositor is conjugate to the specified
intrinsic pullback compositor, for arbitrary composable scheme morphisms.
Source: Stacks Tags 07A6, 0D6D and 0D6E; the ordinary compositor normalization
in `lem-pur-finite-proper-product-transpose`, step 1.
(blueprint: lem-pur-finite-proper-compositor-mate).

Proof: identify the fixed-scalar K-injective compositor with the mate of the
fixed-scalar pullback compositor using right-derived composition conjugacy.
The realization comparison of direct images is fixed on K-injectives and
intertwines the ordinary module adjunctions. Pass these unit/counit equations
through the exact derived realization equivalence. Insert its unit and counit
as in pushModel and iteratedPushModel. Their triangle identities cancel the
middle realization factors. Conjugation is compatible with these adjunction
isomorphisms, leaving exactly kappa.inv on the right and comp.hom on the left.
Thus no arbitrary adjunction or arbitrary compositor is substituted. -/
theorem finiteProperCompositorMate (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (kappa P f g).inv =
      conjugateEquiv ((adj P g).comp (adj P f)) (adj P (f ≫ g))
        (comp P f g).hom := by
  sorry

end WeilConjectures.FiniteProperProduct
