/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/

import Sheaf.AlgebraicGeometry.FineFanBlowup

/-!
# Existence of smooth-functorial saturated fan desingularization

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VIII, Theorems 3.1.27
and 3.2.20, Remark 3.2.21, and construction 3.2.19, pp. 102 and 106
(blueprint: lem-trf-functorial-fan-desingularization).
-/

universe u

namespace AlgebraicGeometry.FineFan

/-- Fine torsion-free fans with finite affine covers admit a smooth-functorial saturated
blowup resolution, including its ordered nonempty coherent centers, smooth terminal fan,
contracted-pullback comparisons, and identity and composition compatibility. In particular
these comparisons apply to open localizations, isomorphisms, and component inclusions in
finite disjoint unions, since their stalk maps are isomorphisms (smooth of rank zero).

Source: ILO, Exposé VIII, Theorems 3.1.27 and 3.2.20, Remark 3.2.21, pp. 102 and 106
(blueprint: lem-trf-functorial-fan-desingularization).

Proof plan:
1. Fix the normalized toric resolution algorithm over the rational numbers, using
   `lem-trf-toric-normalized-desingularization` and
   `def-trf-monoscheme-toric-realization`. Use this same algorithm on all finite disjoint
   unions, so its centers have one synchronized ordering.
2. Descend the toric tower to a monoscheme tower inductively. Torus invariance and
   `lem-trf-toric-monoid-comparison` identify each toric ideal with a unique monoid ideal.
   Nowhere density makes this ideal nonempty on every component. The saturated monoid
   blowup realizes the next normalized toric blowup, and remains fine and torsion free
   with a finite affine cover.
3. By the same comparison lemma, terminal regularity gives terminal monoid smoothness.
   A smooth monoscheme map realizes a smooth toric map. Descend its toric resolution
   comparison center by center; the ideal bijection preserves centers and their order.
   Delete exactly the unit-center isomorphisms, retaining a nontrivial saturation.
4. The toric comparisons respect identities and composition. The ideal bijection and
   canonical blowup chart identifications force the descended comparisons to do so too.
   Iterated deletion records the same ordered subsequence as a single contraction.
5. Apply `lem-trf-sharpening-fan-bijection` to transfer the rule from monoschemes to fans.
   Its finite-disjoint-union synchronization glues one finite global tower, even without
   a global monoscheme lift. It preserves the centers, their order, terminal smoothness,
   and all comparison laws. Finally the special morphisms in the statement are smooth
   of rank zero by `def-trf-fine-fan-blowup`, so the same comparisons apply to them. -/
theorem exists_smoothFunctorialDesingularization :
    Nonempty (SmoothFunctorialDesingularization.{u}) := by
  sorry

end AlgebraicGeometry.FineFan
