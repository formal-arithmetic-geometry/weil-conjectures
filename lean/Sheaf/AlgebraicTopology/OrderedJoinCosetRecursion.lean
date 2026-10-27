/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J5
-/
module

public import Sheaf.AlgebraicTopology.OrderedJoinCosetChains

/-! # Recursive ordered-coset comparison -/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace AlgebraicTopology.OrderedJoin.CosetComparison

variable {G : Type u} [Group G]

/-- The recursive comparison is a chain map through degree n and has a finite
coordinate formula independent of its input values.

Source: ordered-coset comparison, calculations 2–5 of the agent expansion of
six-functors direct-images paragraph (3)
(blueprint: lem-sfb-ordered-join-coset-recursion).

Proof: Check all identities on Finsupp basis vectors. Pair the two orders of
removing positions i<j to obtain d squared zero: their signs are opposite and
the remaining lists agree, including when entries repeat. In degree zero P
sends h to the vertex (0,ha_0), whose boundary is the empty face. Inductively,
z=P(dx) is a cycle by the preceding chain identity and d squared zero.
The partial-contraction identity dS+Sd=id in degree q-1 then gives dP(x)=z;
q<=n ensures this identity is used strictly below the top join degree.
For the coordinate formula start
with the singleton coefficient-one term at color zero and index zero. At
each successor step concatenate the previous finite lists for all faces,
with their alternating signs and coordinate indices reindexed by the
increasing inclusion that skips the deleted position. Expand the contraction
by its color-only insertion/replacement recipe. Retained vertices keep their
indices; every chosen vertex gets index zero. Concatenation retains repeated
terms, so this construction never tests equality of vertices, and its list
is independent of all tuple values. -/
theorem cosetComparisonRecursion (H : Subgroup G) (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (n + 1) → G) :
    (∀ q : ℕ, q ≤ n →
      (boundary (Coset H a) (q : ℤ) (arityDegree q)).comp (comparison H a (q + 1)) =
        (comparison H a q).comp (tupleBoundary H (q : ℤ) (arityDegree q))) ∧
    (∀ q : ℕ, q ≤ n →
      ∃ L : List (ℤ × Symbol (fun _ : Fin (n + 1) ↦ Fin (q + 1)) (q : ℤ)),
        ∀ h : Fin (q + 1) → H,
          comparison H a (q + 1) (tupleTerm (q : ℤ) (List.ofFn h)) =
            (L.map (fun t ↦ t.1 •
              chainMap (fun i j ↦ vertex H a (h j) i) (q : ℤ)
                (Finsupp.single t.2 1))).sum) := by sorry

end AlgebraicTopology.OrderedJoin.CosetComparison
