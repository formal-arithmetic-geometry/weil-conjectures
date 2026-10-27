module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Properties

/-!
# Maximal generalizations in arbitrary subsets of Noetherian schemes

Source: Stacks Project, Properties, Tag 0G2R, `lemma-maximal-points`, assertion (b),
with the definition of its maximal-point subset
(blueprint: lem-sfb-subset-maximal-generalization).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every point of an arbitrary subset of a Noetherian scheme is a specialization of a
point having no proper generalization in that subset. No closedness or constructibility
of the subset is required.

Source: Stacks Project, Properties, Tag 0G2R, `lemma-maximal-points`, assertion (b).
The undefined `T'` in the source's definition of maximal points is read as `T`, as in its proof.
(blueprint: lem-sfb-subset-maximal-generalization)

Proof plan:
1. Local Noetherianity (`pqf-def-locnoeth`) supplies an affine Noetherian neighbourhood of
   each point. The stalk is a localization by `lem-weil-pbc-affine-open-stalk-localization`,
   hence Noetherian by `lem-weil-pbc-localization-noetherian`. It is local because `U` is a
   scheme (`def-pc-scheme`). By `lem-weil-pbc-noetherian-local-finite-krull-dimension`, its
   Krull dimension is a natural number `d(x)`; no uniform bound is needed.
2. By `lem-sc-scheme-stalk-dimension-generalization-chains`, `d(x)` is the supremum of the
   lengths of strict generalization chains starting at `x`. These natural lengths form a
   nonempty bounded set, so the supremum is attained. A proper generalization `y` of `x`
   extends such a chain at `y`, giving `d(y) + 1 ≤ d(x)` and thus `d(y) < d(x)`.
3. Among the points of `T` generalizing `t`, choose `m` of least `d(m)`. This set is nonempty
   because it contains `t`; hence `m ∈ T` and `t ∈ closure {m}`.
4. If `s ∈ T` generalizes `m`, transitivity of specialization makes `s` a generalization of
   `t`. If `s ≠ m`, step 2 contradicts the minimality in step 3. Thus `s = m`.
-/
theorem exists_maximal_generalization_in_subset (U : Scheme.{u})
    [CompactSpace U] [IsLocallyNoetherian U] (T : Set U) (t : U) (ht : t ∈ T) :
    ∃ m ∈ T, t ∈ closure ({m} : Set U) ∧
      ∀ s ∈ T, m ∈ closure ({s} : Set U) → s = m := by
  sorry

end AlgebraicGeometry.Scheme
