/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap

/-!
# The graph comparison under geometric base change

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6 and 07A7
(blueprint: lem-asd-compact-support-graph-geometric-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The forward graph map commutes with the specified compact-support exchange at a
geometric point over an arbitrary scheme. This is equality of unbounded derived
transformations; neither scheme needs to be Noetherian or quasi-compact.
Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6, 07A7, 0E46 and 0E47.
(blueprint: lem-asd-compact-support-graph-geometric-base-change).

Proof:
Pull the compactification graph to the geometric point. The inverse sum exchange and
its graph composition comparison preserve their defining adjunctions. Transpose the two
sheaf projections: on the pulled-back clopen graph both restrict to identity, and on the
complement both restrict to zero. The disjoint-cover sheaf axiom equates the projections;
mate pasting identifies the intervening inverse-image square comparisons. Apply these
sheaf transformations degreewise. Localization full faithfulness descends their equality
to arbitrary unbounded complexes, with the specified exact-functor comparators. Transpose
under the pulled-back proper direct-image adjunction. By the definition of proper exchange
and its counit law, the transpose of the left side is the pulled-back graph projection;
the transpose of the right side is the equal graph projection from the sheaf calculation.
Injectivity of the adjunction hom equivalence proves the equality. This uses equality
before testing stalks, and includes an empty geometric fibre and the zero ring. -/
theorem compactSupportGraphDerivedComparison_geometric_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) (y : X) :
    Functor.whiskerRight
        (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
        (upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y)).mapDerivedCategory ≫
      exactCompactSupportExchange A c (X.algClosurePoint y) =
    (exactEtaleSumExchange A f (X.algClosurePoint y)).hom ≫
      Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A)
          (pullback.snd (X.algClosurePoint y) f)).mapDerivedCategory
        (compactSupportDerivedComparison A (pullback.fst (X.algClosurePoint y) f)
          (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)
          (etaleCompactificationGraphMap A (pullback.fst (X.algClosurePoint y) f)
            (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip))) := by sorry

end AlgebraicGeometry.Etale
