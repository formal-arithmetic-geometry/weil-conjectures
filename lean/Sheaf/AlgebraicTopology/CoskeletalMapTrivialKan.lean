/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Trivial Kan fibrations between coskeletal simplicial sets

Source: Stacks Project, Simplicial Methods, Lemma 14.32.1, Tag 01A6
(blueprint: lem-weil-pbc-coskeletal-map-trivial-kan).
-/

universe u

open CategoryTheory

namespace SSet

/-- Stacks Project, Simplicial Methods, Lemma 14.32.1 (Tag 01A6)
(blueprint: lem-weil-pbc-coskeletal-map-trivial-kan).
A map between `n`-coskeletal simplicial sets which is bijective below `n` and surjective
in degree `n` is a trivial Kan fibration.

Proof: use the boundary lifting characterization of
[def-weil-pbc-trivial-kan-fibration]. First, the map in degree zero is surjective: use the
surjectivity assumption if `n = 0`, and bijectivity below `n` otherwise.
For a boundary lifting problem in degree `1 ≤ k ≤ n`, choose a preimage of the simplex
in the target. Yoneda gives the corresponding map from the standard simplex
[def-weil-pbc-simplicial-set]. It agrees with the given boundary map: every nonsurjective
simplex factors through a face [lem-weil-pbc-simplex-face-factorization], and the two
face values have equal images under the injective map in degree `k - 1 < n`.
For either of the coskeletal objects `W = U, V`, the coskeleton adjunction and the
invertible unit give a bijection between maps `K → W` and maps between their
`n`-truncations [def-weil-pbc-simplicial-coskeleton]. When `k > n`, the boundary inclusion
is an isomorphism in all degrees at most `n`: a map `[j] → [k]` with `j ≤ n < k` cannot
be surjective. Thus restriction from the standard simplex to its boundary induces a
bijection on maps into either `U` or `V`. Extend the given boundary map uniquely into
`V`; its composite with `f` equals the given simplex into `U`, because their restrictions
agree and restriction into `U` is injective. These lifts, including degree zero, give the
right lifting property against every boundary inclusion. -/
theorem rlp_boundaries_of_coskeletal_map {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)
    (hbij : ∀ i : ℕ, i < n → Function.Bijective (f.app (Opposite.op (SimplexCategory.mk i))))
    (hsurj : Function.Surjective (f.app (Opposite.op (SimplexCategory.mk n))))
    (hU : IsIso ((coskAdj n).unit.app U))
    (hV : IsIso ((coskAdj n).unit.app V)) :
    modelCategoryQuillen.I.rlp f := by
  sorry

end SSet
