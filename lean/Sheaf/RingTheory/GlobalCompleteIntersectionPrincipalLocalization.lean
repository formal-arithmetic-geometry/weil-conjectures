/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.CompleteIntersectionOverField
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import Sheaf.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Principal localization of a global complete intersection

Source: Stacks Project, Algebra, Lemma Tag 00SA (lemma-localize-lci), part (1)
(blueprint: lem-weil-pbc-global-complete-intersection-principal-localization).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A principal localization of a global complete intersection over a field is a global
complete intersection over that field.

Source: Stacks Project, Algebra, Lemma Tag 00SA (lemma-localize-lci), part (1)
(blueprint: lem-weil-pbc-global-complete-intersection-principal-localization).

Proof: If the localization is zero, use the zero-ring clause of
`IsGlobalCompleteIntersection`. Otherwise choose a polynomial presentation of `T` from the
hypothesis, identify `T` with its quotient, and lift `g` to a polynomial `h`. The localization
is presented by adjoining one variable `y` and the relation `hy - 1`; the kernel calculation
uses the polynomial coefficient kernel and the localization polynomial quotient lemma. The
Krull dimension is unchanged on the principal open, by the localization homeomorphism and
invariance of local dimensions, so the presentation has one more variable and one more relation
with the required dimension. -/
theorem isGlobalCompleteIntersection_localizationAway
    (k : Type u) (T : Type v) [Field k] [CommRing T] [Algebra k T]
    (hT : IsGlobalCompleteIntersection k T) (g : T) :
    IsGlobalCompleteIntersection k (Localization.Away g) := by
  sorry

end Algebra
