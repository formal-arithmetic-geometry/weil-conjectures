/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Constructible

/-!
# Images of inverse limits in constructible subsets

Source: Stacks Project, Limits of Schemes, Lemma 05F4 in Situation 086P,
restricted to constructible subsets
(blueprint: lem-weil-pbc-limit-contained-in-constructible).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A constructible subset containing the image of the limit of a directed inverse system
of quasi-compact quasi-separated schemes with affine transition maps contains the images
of every sufficiently large stage.

Source: Stacks Project, Limits of Schemes, Lemma 05F4 in Situation 086P
(blueprint: lem-weil-pbc-limit-contained-in-constructible).

Proof plan:
1. If the target stage is affine, express the constructible complement of `E` as the
   image of an affine scheme `W` (def-weil-constructible-subset and
   lem-weil-pbc-constructible-is-image).
2. The fibre product of `W` with the limit is empty: its two projections would map
   any point both into `E` and into its complement (def-pc-fibre-product).
3. Over the tail of the index set, the fibre products of `W` with the stages form
   an inverse system whose limit is this empty fibre product
   (lem-weil-pbc-scheme-over-limit and lem-weil-pbc-limit-affine-transition).
   They are affine, hence quasi-compact (lem-weil-pbc-affine-morphism-permanence).
4. Some such fibre product is empty by lem-weil-pbc-limit-nonempty, and every
   later fibre product maps to it and is therefore empty as well.
5. A point outside `E` at a later stage would lift to the fibre product: the tensor
   product of the two residue fields over their common residue field is nonzero
   and has a prime (lem-weil-pbc-fibre-product-points). This proves the affine case.
6. Cover the target stage by finitely many affine opens. The preimage opens form
   inverse systems with the corresponding open in the limit as their limit
   (lem-weil-pbc-limit-cone-affine-projections-opens). Their stages are affine,
   and `E` restricts to a constructible subset of each affine open
   (lem-weil-pbc-constructible-open-restriction). Apply the affine case to each.
7. Directedness supplies a common upper bound of the finitely many resulting
   indices, also above the original index. The images of all stages above it
   are contained in `E`, because the preimage opens cover each stage. -/
theorem exists_eventually_range_subset_of_isConstructible
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ j : Iᵒᵖ, CompactSpace (D.obj j)]
    [∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (E : Set (D.obj (op i))) (hE : Topology.IsConstructible E)
    (himage : Set.range (c.π.app (op i)) ⊆ E) :
    ∃ i₁ : I, ∃ hi₁ : i ≤ i₁, ∀ (j : I) (hj : i₁ ≤ j),
      Set.range (D.map (homOfLE (hi₁.trans hj)).op) ⊆ E := by
  sorry

end AlgebraicGeometry
