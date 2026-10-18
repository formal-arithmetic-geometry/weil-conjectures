/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Gleason's characterization of Stonean spaces

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-pe-stonean/det-pe-stonean-projective.md
(blueprint: det-pe-stonean-projective).
-/

@[expose] public section

universe u

open Function

namespace CompactT2

/-- For a compact Hausdorff space, extremal disconnectedness, projectivity for
compact Hausdorff surjections, and the existence of sections of all such
surjections are equivalent.  An extremally disconnected space is also totally
disconnected and therefore is a profinite space with its given compact
Hausdorff structure.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-pe-stonean/det-pe-stonean-projective.md (blueprint: det-pe-stonean-projective).

The same characterization is Stacks Project, Topology, Tag 08YN; total
disconnectedness and profiniteness follow Tags 08YI and 08ZY.

Proof, following the node's fourteen steps:
1. For (2) implies (3), lift the identity of `S` through `q`.
2. For (3) implies (2), form `P = {(s,x) | f(s) = p(x)}` in `S × X`.
The product is compact by `lem-weil-pbc-tychonoff-product-quasi-compact` and
Hausdorff by separation in a coordinate. The equalizer is closed by Hausdorff
separation in `Y`, hence compact by `lem-weil-pbc-closed-in-quasi-compact`
and Hausdorff as a subspace.
3. The first projection is continuous and surjective. A section followed by
the second projection gives the desired lift, by the defining equality of `P`.
4. For (3) implies (1), the closure of an open `U` and its complement are
closed compact Hausdorff subspaces, using `lem-weil-pbc-closed-in-quasi-compact`.
Their disjoint union is compact Hausdorff by finite subcovers and separation
within and between summands, and its inclusions define a continuous surjection.
5. The inverse image under a section of the first summand is clopen, contains
`U`, hence contains its closure, and is contained in that closure. Thus the
closure of `U` is open.
6. For (1) implies (3), consider closed subsets of `P` surjecting onto `S`.
The intersection of a nonempty chain still surjects: intersect the chain
with each closed fiber and apply the finite intersection property, proved
by the finite-subcover definition of compactness. For the empty chain use `P`.
7. Complementation turns these lower bounds into upper bounds. Apply
`lem-weil-pbc-zorn-lemma` to obtain a minimal closed surjecting subset `P₀`.
It is compact by `lem-weil-pbc-closed-in-quasi-compact` and Hausdorff as a subspace.
8. The restriction `q₀` is closed: a closed subset is compact by
`lem-weil-pbc-closed-in-quasi-compact`; separate its image from an external
point using finitely many Hausdorff neighborhoods and compactness.
9. For open `V` in `P₀`, set `V* = S \ q₀(P₀ \ V)`. It is open and consists
of points whose whole nonempty fiber is in `V`. Hence it lies in `q₀(V)`,
is nonempty when `V` is nonempty by minimality, and is monotone in `V`.
10. If `a ∈ A` with `A` open, every neighborhood `N` of `q₀(a)` meets `A*`:
apply step 9 to the nonempty open `A ∩ q₀⁻¹(N)`. Thus `q₀(a)` is in its closure.
11. Distinct points in a fiber have disjoint open neighborhoods `A,B`.
Their stars are disjoint, but both closures contain the common image.
Extremal disconnectedness makes the first closure open, forcing it to meet
`B*`, whereas an open set disjoint from `A*` misses its closure. Contradiction.
12. Thus `q₀` is a continuous bijection and a homeomorphism by
`lem-weil-pbc-compact-hausdorff-bijection`. Its inverse followed by the inclusion
of `P₀` gives a continuous section of `q`.
13. Disjoint open neighborhoods of distinct points yield a clopen closure
separating them. A connected subset cannot contain both points, so `S` is
totally disconnected.
14. For profiniteness, use finite partitions into nonempty clopen blocks,
ordered by refinement. Intersections give common refinements. The canonical
map to the inverse limit is continuous by its coordinates and injective by
clopen separation. A compatible family of blocks has the finite intersection
property; compactness gives a point in all of them, proving surjectivity.
The limit is Hausdorff by coordinate separation, so
`lem-weil-pbc-compact-hausdorff-bijection` makes this map a homeomorphism.
For empty `S`, use the diagram consisting of the empty finite discrete space. -/
theorem extremallyDisconnected_iff_projective_iff_section
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S] :
    (ExtremallyDisconnected S ↔ CompactT2.Projective S) ∧
      (CompactT2.Projective S ↔
        ∀ (P : Type u) [TopologicalSpace P] [CompactSpace P] [T2Space P]
          (q : P → S), Continuous q → Surjective q →
            ∃ σ : S → P, Continuous σ ∧ q ∘ σ = id) ∧
      (ExtremallyDisconnected S → TotallyDisconnectedSpace S) := by
  sorry

end CompactT2
