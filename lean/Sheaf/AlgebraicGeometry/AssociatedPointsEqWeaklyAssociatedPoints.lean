/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.RingTheory.WeaklyAssociated
import Sheaf.AlgebraicGeometry.AssociatedWeaklyAssociated

/-!
# Associated and weakly associated points of the structure sheaf

Source: Stacks Project, Divisors, Lemma 31.5.8 (Tag 05AR)
(blueprint: lem-sc-ass-weakass-locally-noetherian).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- On a locally Noetherian scheme, the associated points of the structure sheaf equal its
weakly associated points. Association means that the maximal ideal of the stalk is an
annihilator, and weak association means that it is minimal over an annihilator.
Source: Stacks Project, Divisors, Lemma 31.5.8 (Tag 05AR)
(blueprint: lem-sc-ass-weakass-locally-noetherian).

Proof:
1. For each point `x`, the stalk is Noetherian, so its maximal ideal is finitely generated
   (`lem-sc-locnoeth-stalk-maxideal-fg`).
2. Apply `lem-sc-ass-weakass-fg-stalk` (the first assertion of Tag 05AR) to the quasi-coherent
   structure sheaf at `x`. Its stalk is the local ring itself. The finite generation from
   step 1 gives equivalence of association and weak association at every point, hence
   equality of the two sets. -/
theorem associatedPoints_eq_weaklyAssociatedPoints
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    {x : X | ∃ a : X.presheaf.stalk x,
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        (⊥ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)).colon {a}} =
      {x : X | IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        Ideal.WeakAss (X.presheaf.stalk x)} := by
  sorry

end AlgebraicGeometry.Scheme
