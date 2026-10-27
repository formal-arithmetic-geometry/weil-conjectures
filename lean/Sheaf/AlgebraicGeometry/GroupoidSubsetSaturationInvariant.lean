/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Invariance of subset saturation in a scheme groupoid

Source: Stacks Project, Groupoids, Tag 03LO, part (1), and the subset-invariance
equivalence following Tag 03BC (blueprint: lem-sfb-groupoid-subset-saturation-invariant).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Saturating any subset of the points of a scheme groupoid gives an invariant subset.
No openness, finiteness, flatness or separation condition is imposed on either map.

Source: Stacks Project, Groupoids, Tag 03LO (lemma-constructing-invariant-opens),
part (1), and the equivalence following Tag 03BC (definition-invariant-open).
(blueprint: lem-sfb-groupoid-subset-saturation-invariant).

Proof:
1. Put B = t(s⁻¹(A)). If s(r) belongs to B, choose a with s(a) in A and t(a) = s(r).
   Apply lem-weil-pbc-base-change-image, namely Scheme.image_preimage_eq_of_isPullback,
   to the square R ×_{s,U,t} R and the singleton {r}. It gives a point z with first
   projection r and second projection a. This is a scheme fibre-product image identity;
   no identification with the topological fibre product is needed.
2. The composition laws of def-a1-groupoid-scheme give s(c(z)) = s(a) and
   t(c(z)) = t(r). Thus c(z) witnesses t(r) in B, proving s⁻¹(B) ⊆ t⁻¹(B).
3. If t(r) belongs to B, the inverse laws of def-a1-groupoid-scheme give
   s(i(r)) = t(r) and t(i(r)) = s(r). Apply step 2 to i(r) to get s(r) in B.
   This proves the reverse inclusion. Only the scheme pullback image identity and
   the groupoid identities were used.
-/
theorem IsGroupoidScheme.subset_saturation_invariant
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (_hG : IsGroupoidScheme s t e i c) (A : Set U) :
    s ⁻¹' (t '' (s ⁻¹' A)) = t ⁻¹' (t '' (s ⁻¹' A)) := by
  sorry

end AlgebraicGeometry
