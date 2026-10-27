/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.SmallSingularLocusResolutionRule
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.InvertibleCenter

/-! # Strong resolution for pairs with small singular locus

Source: Temkin, Non-embedded Desingularization, Theorem 3.4.1 and §3.4.2,
printed pp.25–26 (blueprint: lem-per-small-singular-locus-resolution).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- A single strong resolution rule exists for all pairs with small singular locus.
Source: Temkin, Theorem 3.4.1, using §§1.3.1–1.3.2 and 2.3.5 for the strong variety input
(blueprint: lem-per-small-singular-locus-resolution).

Proof:
1. Complete X along its Cartier divisor D, using
   lem-per-small-divisor-formal-completion. This is a reduced Noetherian quasi-excellent
   rig-regular locally principal formal scheme, a finite disjoint union of formal varieties.
   Apply the single formal rule of lem-per-rig-regular-formal-resolution.
2. Use lem-per-supported-formal-blowup-algebraization to algebraize the ordered supported
   tower uniquely. Its coherent centers are nonempty and regular. The singular-support
   clause gives the regular last level and centers over the singular locus of X; the
   reduced-input clause gives nowhere density. The empty input gives length zero.
3. For a regular morphism of pairs, lem-per-regular-morphism-formal-completion gives a
   regular completed morphism preserving the distinguished ideals. The formal rule pulls
   back with exactly the empty centers deleted and all other ideals retained in order.
4. The level projections in the ordinary pullback are flat by
   lem-weil-pbc-flat-morphism-base-change. By thm-nagata-blowup-flat-base-change each step
   is the blowup of the extended ideal. Completing identifies this ordinary tower with the
   uncontracted formal pullback: modulo a power of the divisor ideal both center pullbacks
   extend the same quotient ideal, by lem-per-supported-formal-blowup-algebraization.
5. A supported ordinary center is empty exactly when its formal center is empty. Its ideal
   is then unit, and cor-nagata-blowup-cartier-iso makes its blowup an isomorphism. Delete
   exactly these stages. Unique algebraization identifies the resulting ordered tower
   with the tower for the source pair, including every retained ideal. This asserts no
   independence from the auxiliary divisor.
-/
theorem exists_smallSingularLocusResolutionRule :
    Nonempty SmallSingularLocusResolutionRule.{u} := by
  sorry

end AlgebraicGeometry
