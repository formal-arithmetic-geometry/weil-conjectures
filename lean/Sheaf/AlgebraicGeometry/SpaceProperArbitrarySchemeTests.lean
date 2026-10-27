/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal

/-! # Properness of arbitrary algebraic-space maps tested on schemes

Source: Stacks Project, Morphisms of Spaces, Tag 083R, lemma-proper-local, (1) iff (2)
(blueprint: lem-sfb-space-proper-arbitrary-scheme-tests).

Properness is the intrinsic algebraic-space predicate. The pullback is the existing
sheaf fibre product bundled as an algebraic space, with its actual second projection.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An arbitrary algebraic-space map is proper exactly when all its pullbacks to schemes
are proper; the pulled-back source remains an algebraic space.

Source: Stacks Project, Morphisms of Spaces, Tag 083R, lemma-proper-local, (1) iff (2)
(blueprint: lem-sfb-space-proper-arbitrary-scheme-tests).

Proof:
1. Properness is preserved by base change [lem-sfb-space-proper-base-change], giving
   the forward implication. The quasi-compact atlas formulation there agrees with
   topological quasi-compactness by [lem-a1-space-etale-open-image].
2. Conversely choose a surjective etale scheme atlas V of Y [def-trf-algebraic-space].
   The hypothesis makes X_V -> V proper. Using quasi-compact scheme atlases from
   [lem-a1-space-etale-open-image], apply etale locality of quasi-compactness and
   separatedness [lem-trf-space-qc-separated-etale-local] to descend these properties
   to q. Atlas surjectivity on points is [lem-a1-space-point-open-calculus].
3. Choose a surjective etale scheme atlas U of X_V. The chart criterion
   [lem-sfb-space-local-properties-chart-test], first over V and then over Y, gives
   local finite type of q. Together with quasi-compactness this is finite type
   [def-sfb-space-morphism-properties].
4. For any algebraic space Z -> Y and closed C in |X x_Y Z|, choose an etale
   surjective scheme atlas p : W -> Z. Pullback associativity
   [lem-trf-space-fibre-products-etale-covers] identifies the pullback over W with
   X x_Y W, whose projection k to W is proper by hypothesis. Its image D of the
   inverse image of C is closed. Continuity and compatible-pair lifting on point
   fibre products [lem-a1-space-point-open-calculus] give D = |p|^{-1}(|h|(C)),
   where h : X x_Y Z -> Z is the projection.
5. The point map of p is open and surjective [lem-a1-space-point-open-calculus].
   Thus the complement of |h|(C) is the open image of the complement of D.
   Consequently h is closed. As Z was arbitrary, q is universally closed.
   Combine this with step 3 and separatedness using [def-sfb-space-morphism-properties]. -/
theorem proper_iff_scheme_tests {S : Scheme.{u}} {X Y : AlgebraicSpace S} (q : X ⟶ Y) :
    MapIsProper q ↔
      ∀ (T : Over S) (g : schemeSpace T ⟶ Y),
        MapIsProper (ObjectProperty.homMk (Limits.pullback.snd q.hom g.hom) :
          enlargedFibreProduct q g ⟶ schemeSpace T) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
