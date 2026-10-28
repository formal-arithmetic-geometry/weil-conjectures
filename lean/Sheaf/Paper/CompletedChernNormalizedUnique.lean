/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalP1ScalarChernMaps

/-! Uniqueness of the normalized completed Chern adjunct. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

/-- A normalized completed Chern adjunct is unique because the presentation's
source comparison is an isomorphism.

The normalization equation is an equality after postcomposition with
`p.sourceMap`.  That map is the canonical shifted derived comparison and is
invertible by its construction, so cancellation identifies any two normalized
adjuncts.
(blueprint: lem-sfb-rational-p1-scalar-chern-base-change-chern-none) -/
theorem completedChernNormalized_unique
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S}
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (a a' : DiagonalTrace.completedUnit l S ⟶
      p.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l p a)
    (ha' : CompletedChernNormalized l p a') : a = a' := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
