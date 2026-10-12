/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover

/-!
# Descent of separatedness along a flat surjective quasi-compact morphism

Source: Stacks Project, Descent, Lemma Tag 02KU (lemma-descending-property-separated),
the descent direction for a one-member fpqc covering
(blueprint: lem-weil-pbc-fpqc-descend-separated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separatedness descends along a flat surjective quasi-compact base change.
Source: Stacks Project, Descent, Tag 02KU, with Topologies Tag 03L7 (2).
(blueprint: lem-weil-pbc-fpqc-descend-separated)

Proof:
1. The diagonal of `pullback.snd f g` is a closed immersion by separatedness, hence
   universally closed (lem-weil-pbc-closed-immersion-integral-separated-uc, clause (d)).
2. Identify that diagonal with the base change of the diagonal of `f` along the projection
   `(X ×_S X) ×_S S' → X ×_S X` (lemma-nagata-diagonal-base-change). The square is cartesian
   by lem-weil-pbc-cartesian-square-pasting; the target identification is an isomorphism,
   hence universally closed, so the induced diagonal is universally closed as well
   (lem-weil-pbc-closed-immersion-integral-separated-uc, clauses (d) and (f)).
3. This projection is flat, surjective and quasi-compact by base change
   (lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-surjective-base-change,
   lem-weil-pbc-qcqs-morphism-permanence, clause (3)). For every affine open of its target,
   its preimage is quasi-compact and has a finite affine cover whose images cover that open.
   Thus it forms a one-member fpqc covering (def-weil-pbc-fpqc-covering; Tag 03L7 (2)).
4. Universal closedness of the diagonal descends along this covering
   (lem-weil-pbc-fpqc-descend-universally-closed, Tag 02KS). Uniqueness of fibre products
   identifies the chosen base change with the cartesian square in step 2; compositions
   with these isomorphisms preserve universal closedness.
5. The original diagonal therefore has closed image. It is an immersion
   (lem-weil-pbc-diagonal-immersion, Tag 01KJ), so it is a closed immersion
   (lem-weil-pbc-immersion-closed-image-closed-immersion, Tag 01IQ). This is separatedness.
-/
theorem isSeparated_of_flat_surjective_baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]
    [IsSeparated (pullback.snd f g)] : IsSeparated f := by
  sorry

end AlgebraicGeometry
