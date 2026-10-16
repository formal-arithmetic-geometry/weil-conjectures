/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-! Proper étale derived direct image and coproducts.

Source: SGA 4, Exp. XVIII, Theorem 3.1.4; Stacks Project, Tag 0F5Y.
(blueprint: lem-etale-proper-derived-lower-star-coproducts)
-/

@[expose] public section

set_option autoImplicit false

universe u' u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- For a proper morphism, the total right derived direct image preserves all coproducts.

Source: SGA 4, Exp. XVIII, Theorem 3.1.4; Stacks Project, Tag 0F5Y.
(blueprint: lem-etale-proper-derived-lower-star-coproducts-for-grothendieck)

Proof in words: direct image along a proper morphism has finite cohomological amplitude on each
quasi-compact étale open, and its higher direct images commute with filtered colimits. Therefore
its total right derived functor commutes with arbitrary coproducts. Restriction to quasi-compact
opens detects isomorphisms, so the local comparisons assemble to the global coproduct comparison.
The derived categories of sheaves of objects of a Grothendieck abelian category have the required
coproducts, and this preservation statement is the input to Brown representability.
-/
theorem proper_rightDerivedLowerStar_preservesCoproducts_for_grothendieck
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g] :
    ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((g)_*[A]).rightDerivedFunctor := by
  sorry

end AlgebraicGeometry.Etale
