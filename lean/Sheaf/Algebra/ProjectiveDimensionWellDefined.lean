/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.RingTheory.GlobalDimension

/-!
# Projective and global dimension are well defined

Source: Stacks Project, Algebra, Definitions 00O4 and 00O6
(blueprint: lem-weil-pbc-projective-dimension-well-defined).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Padding a finite projective resolution by zeros preserves its exactness and
projectivity, and finite projective and global bounds have least values.
Source: Stacks Project, Algebra, Definitions 00O4 and 00O6
(blueprint: lem-weil-pbc-projective-dimension-well-defined).

A finite resolution `0 → P_n → ⋯ → P_0 → M → 0` is encoded, as in the recorded
`ModuleCat.HasProjectiveResolutionLE`, by its zero continuation: a
`ProjectiveResolution` of `M` whose terms in degrees above `n` are zero. Putting
`P_i = 0` for `n < i ≤ m` therefore leaves the same resolution `P` (same terms,
differentials and augmentation), and clause (1) says that `P` is then a projective
resolution of length at most `m`: its terms in degrees above `m` are zero.

Proof, following the five steps of the node:
1. Retain the supplied resolution and its zero continuation. Each newly included
   term is zero, hence projective (`def-weil-pbc-projective-module`). Composites
   through these terms vanish, and image and kernel there are both zero
   (`def-weil-pbc-exact-sequence`). Exactness at the old leftmost term is its
   original injectivity; all other old neighbouring maps are unchanged. This
   includes `n = 0` and `m = n`.
2. The set of lengths admitting a resolution contains `n`, hence has a least
   natural number `d` by the least-number principle.
3. Membership at `k` implies `d ≤ k` by minimality. Conversely, pad a resolution
   of length `d` to length `k` using step 1.
4. The set of uniform bounds for all modules is nonempty by hypothesis, hence
   has a least natural number `g` by the same least-number principle.
5. A uniform bound `k` implies `g ≤ k` by minimality. Conversely, apply step 1
   to the length-`g` resolution of each module to obtain the uniform bound `k`. -/
theorem projective_and_global_dimension_well_defined
    {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R) (m n : ℕ) (hnm : n ≤ m) :
    (∀ P : ProjectiveResolution M,
      (∀ i : ℕ, n < i → IsZero (P.complex.X i)) →
        ∀ i : ℕ, m < i → IsZero (P.complex.X i)) ∧
    (HasProjectiveResolutionLE M n →
      ∃ d : ℕ, HasProjectiveResolutionLE M d ∧
        ∀ k : ℕ, HasProjectiveResolutionLE M k ↔ d ≤ k) ∧
    ((∃ b : ℕ, Ring.HasGlobalDimensionLE.{u, max u v} R b) →
      ∃ g : ℕ, Ring.HasGlobalDimensionLE.{u, max u v} R g ∧
        ∀ k : ℕ, Ring.HasGlobalDimensionLE.{u, max u v} R k ↔ g ≤ k) := by
  sorry

end ModuleCat
