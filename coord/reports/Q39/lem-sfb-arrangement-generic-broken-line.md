## Worker report

The module `Sheaf.Geometry.ArrangementGenericBrokenLine` states
`AffineSubspace.arrangement_generic_broken_line`, with its only proof `sorry`.
No definition or auxiliary theorem is introduced. The item is unchanged outside `lean`.

Source read: Milne, Algebraic Groups, Appendix C.8--C.10 and C.19--C.22,
printed pp.609--612 (PDF pages 621--624). These give chamber terminology, not this
finite-affine-arrangement theorem; the node correctly identifies its proof as an agent
supporting argument. All seven proof steps are reproduced in the declaration docstring.
The node has no blueprint update; the current blueprint is `literature/blueprint/latest`.

Hypotheses and clauses, matched in order:

- `E : Type u`, `[AddCommGroup E]`, `[Module ℝ E]`, `[FiniteDimensional ℝ E]` give
  an arbitrary finite-dimensional real vector space. `[TopologicalSpace E]`,
  `[IsTopologicalAddGroup E]`, `[ContinuousSMul ℝ E]`, `[T2Space E]` give its usual
  finite-dimensional topology: finite-dimensional Hausdorff real vector-space topologies
  are the standard one, as in the recorded continuity dependency. No norm or inner product
  is chosen, and there is no restriction on the universe of E.
- `ℋ : Finset (AffineSubspace ℝ E)` is a finite set, so has distinct members, not a possibly
  repeated indexed family. `hℋ` requires every member to be nonempty and
  `Module.finrank ℝ H.direction + 1 = Module.finrank ℝ E`. This is precisely a translate
  of a codimension-one linear subspace. Nonemptiness excludes Mathlib's empty affine
  subspace, which is not a hyperplane even when its zero direction has codimension one.
- The regular locus is the inline set `{q : E | ∀ H ∈ ℋ, q ∉ H}`. This is exactly
  the complement of the union of all walls. It is not a new definition of a notion.
- The first conjunct says `∀ O, IsOpen O → O.Nonempty → ∃ q ∈ O, ∀ H ∈ ℋ, q ∉ H`:
  every nonempty open set meets the regular locus, without convexity required here.
- The second conjunct quantifies over all nonempty open convex `U`, `x ∈ U`, `y ∈ U`,
  and regularity of both endpoints, exactly as the node does. `Convex ℝ U` is Mathlib's
  usual segment-containment predicate.
- The bend is `∃ z`, with `z ∈ U` and `∀ H ∈ ℋ, z ∉ H`. The additional witness
  `γ : Path x y` is fixed by the equality
  `γ = (Path.segment x z).trans (Path.segment z y)`; it is the canonical broken line,
  not a separately chosen path. Its segment union is explicitly required to lie in `U`.
- For every distinct pair `H,K ∈ ℋ`, `Disjoint` of this segment union and `H ∩ K`
  expresses avoidance of all pairwise intersections, including at the bend and endpoints.
- For each ordered leg `(a,b) = (x,z)` or `(z,y)` and each wall, every zero parameter
  `t ∈ Set.Icc 0 1` of `AffineMap.lineMap a b` belongs to `Set.Ioo 0 1`, has
  `H.SOppSide a b`, and is the unique zero parameter in `Set.Icc 0 1`. Thus there is
  at most one meeting on each leg, necessarily interior, and the leg crosses between
  opposite strict sides. `lineMap_apply_module` gives `(1-t) • a + t • b`, the node's
  specified parameterization. Uniqueness is per leg; recrossing on the other leg is allowed.
- The finite component sequence is `C : Fin (n+1) → Set E`, for `n : ℕ`. Each `C i`
  equals `connectedComponentIn` of the regular locus at a regular point. This is Mathlib's
  maximal connected subset, not an arbitrary connected subset. The first and last
  components are explicitly those of `x` and `y`.
- The ordered division times `t : Fin (n+2) → ℝ` satisfy `StrictMono t`, `t 0 = 0`,
  and `t (Fin.last (n+1)) = 1`. For every component index `i`, all values of the actual
  concatenated path on `(t i.castSucc, t i.succ)` lie in `C i`. Thus this is the component
  sequence of this very path in traversal order. It has neither extraneous path portions
  nor missing crossings. The bend need not be a division time since it is regular.
- At internal division time `t i.succ.castSucc`, for `i : Fin n`, the path lies on a wall
  `H ∈ ℋ` and on no other wall, and lies in the closures of `C i.castSucc` and `C i.succ`.
  All points of those adjacent components lie on opposite strict sides of `H` and on
  the same strict side of each `K ≠ H`. This is separation by exactly that wall at the
  specified crossing point. Closures ensure actual incidence at that point, rather
  than just a combinatorial sign change. Every division time is a crossing, and every
  other interior time lies in a regular component.
- The final conjunct `Module.finrank ℝ E = 0 → ℋ = ∅` includes the dimension-zero
  assertion. No nonconstant-path hypothesis occurs: singleton spaces, constant legs,
  `z = x`, `z = y`, `x = y`, and the constant broken line are all permitted.

Dependency declarations read and used:

- Statement dependency `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`, docstring and signature at lines 49--63.
  This module is a public import; codimension is rendered using the recorded dimension.
- Proof dependency `lem-sfb-finite-dimensional-linear-map-continuous`:
  `LinearMap.continuous_of_finiteDimensional`,
  `Mathlib.Topology.Algebra.Module.FiniteDimension`, lines 282--285; its full signature
  and surrounding finite-dimensional Hausdorff hypotheses were read. Plain proof import.
- Proof dependency `lem-pc-finite-linear-avoidance`:
  `Subspace.biUnion_ne_univ_of_top_notMem`, `Mathlib.GroupTheory.CosetCover`,
  lines 376--386, including infinite-field and module binders. Plain proof import.
- Proof dependency `lem-sfb-convex-set-connected`: `Convex.isConnected`,
  `Mathlib.Analysis.Convex.PathConnected`, lines 89--92, including the file's topological
  vector-space binders. The module is a public import because it also supplies
  `Path.segment` in the signature.
- Further Mathlib notions: `AffineSubspace` and `.direction` in
  `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` (149--153, 231--237),
  `.SOppSide` and `.SSameSide` in `Mathlib.Analysis.Convex.Side` (45--61),
  `AffineMap.lineMap` in `Mathlib.LinearAlgebra.AffineSpace.AffineMap` (481--484),
  `segment` in `Mathlib.Analysis.Convex.Segment` (50--52), and
  `connectedComponentIn` in `Mathlib.Topology.Connected.Basic` (497--506).
  `Path.extend` is the canonical real-parameter extension of a bundled path; all
  division times are in [0,1] by strict monotonicity and the endpoint equalities.

Edge cases checked before writing: dimension zero (no nonempty codimension-one direction);
empty arrangement in any dimension (regular locus is all of E and `n = 0` is allowed);
`x = y` and constant legs (no wall meets a regular constant leg); dimension one
(hyperplanes are distinct points and have empty pairwise intersections); parallel distinct
walls (empty intersections impose no exclusions); concurrent walls in the plane
(the bend excludes their simultaneous intersections); and a wall crossed once on each
leg (per-leg uniqueness permits it, and nonadjacent components may repeat).
The gallery permits `n = 0`: two distinct division times 0 and 1 and one component.
No `Nontrivial E`, positive-dimensional, or nonempty-arrangement hypothesis was added.

Searches actually run, through the prescribed `msearch.py Q39` wrapper:

- LeanFinder: "A generic broken line with two segments joins points in the complement of
  finitely many affine hyperplanes, crossing one hyperplane at a time". Eight hits:
  `IsVisible`, `isVisible_iff_lineMap`, `Configuration.Nondegenerate.exists_line`,
  `IsClosed.exists_wbtw_isVisible`, `AffineSubspace.SOppSide.exists_sbtw`,
  `openSegment_subset_union`, and the two strict-side connectedness theorems.
  These give related notions or one segment, not the node's complete generic bend/gallery.
- Loogle: `AffineSubspace, segment`. No hits.
- Grep: `IsHyperplane|isHyperplane|broken.line|arrangement`, under `LinearAlgebra`.
  One irrelevant rearrangement comment in `Finsupp/LSum.lean`; no exact statement.
- LeanSearch: "A two segment path in the complement of a finite hyperplane arrangement
  crosses the walls one at a time". Eight hits on `Path`, `Path.ofLine`, `Path.segment`,
  `Path.trans`, its application formula, a path-through-family theorem and quiver paths.
  None supplies generic avoidance or the gallery.
- Direct `rg` in Mathlib for hyperplanes, strict sides and connected components located
  the notions above, but no finite-arrangement theorem. Direct searches of both
  `lean/WeilConjectures` and `lean/Sheaf` for arrangement, broken line, generic path,
  hyperplane and the item id found no exact declaration. A declaration-name search in
  Mathlib, both project roots and `dag/lean_names_upstream.json` found no name collision.
- DAG search for affine hyperplanes and broken lines found the item, its topology
  proof dependency, and its root-marked consumer, with no duplicate definition needed.

There are no new nodes, dependency repairs, statement corrections or disputed statements.

## Second reading by Q39

The delivered section of this name was an in-thread self-check by the worker (no independent
reader). It is replaced by the independent maintainer second reading below (cc reviewer,
2026-10-24). The Lean file and node are unchanged.

Node statement as a list, with the Lean that renders it and the verdict:

1. E a finite-dimensional real vector space with its usual topology: `E : Type u`,
   `[AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace E]
   [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]`. A Hausdorff topological
   vector-space topology on a finite-dimensional real space is the standard one (the binders
   of the cited continuity leaf `LinearMap.continuous_of_finiteDimensional`). Correct; no
   universe restriction.
2. A finite set of distinct affine hyperplanes: `ℋ : Finset (AffineSubspace ℝ E)` with
   `(H : Set E).Nonempty ∧ finrank H.direction + 1 = finrank E`. Translate of a codimension-one
   linear subspace; nonemptiness correctly excludes `⊥`. Correct.
3. E_reg: inline `{q | ∀ H ∈ ℋ, q ∉ H}`. Correct (no DAG node owns this notion).
4. E_reg meets every nonempty open set: first conjunct. Correct, no convexity.
5. U nonempty, open, convex, x, y ∈ U ∩ E_reg: binders of the second conjunct. Correct.
6. ∃ z ∈ U ∩ E_reg, broken line avoiding every H ∩ H' (H ≠ H'): `z ∈ U`, `∀ H ∈ ℋ, z ∉ H`,
   `γ` pinned to `(Path.segment x z).trans (Path.segment z y)`, `Disjoint (segment ℝ x z ∪
   segment ℝ z y) (H ∩ K)`. The extra clause `segments ⊆ U` follows from convexity. Correct.
7. Each segment meets each hyperplane at most once, in its interior, crossing strict sides:
   the per-leg clause over `(a,b) ∈ {(x,z),(z,y)}` with `t ∈ Ioo 0 1`, `H.SOppSide a b`, and
   uniqueness in `Icc 0 1`. `lineMap a b t = (1-t)a + tb`. For a hyperplane `f_H = 0`,
   `SOppSide`/`SSameSide` (Mathlib `Analysis/Convex/Side.lean:50,58`, via `SameRay` of
   displacement vectors) is exactly opposite/equal strict signs of `f_H`. Correct.
8. Finite sequence of components from that of x to that of y, consecutive ones separated by
   just one hyperplane at a point on no other: `n`, strictly monotone `t` from 0 to 1,
   `C i = connectedComponentIn E_reg p` at regular `p`, `C 0`/`C last` at x/y, path portions
   between division times in `C i`, and at each internal time a unique wall `H` containing the
   point, closure incidence with both neighbours, `SOppSide` for `H` and `SSameSide` for every
   other wall on all points of the two components. Since components of E_reg are exactly the
   global sign regions (proof step 6), these clauses are true and say what the node says;
   `i.succ.castSucc` indexes the internal times 1..n. Correct.
9. dim E = 0: `finrank ℝ E = 0 → ℋ = ∅`, and the constant path is allowed because no clause
   forbids `n = 0`, `z = x`, `x = y`. Correct.

Edge cases: dim 0 (hℋ unsatisfiable, ℋ = ∅, E a point); empty arrangement in positive
dimension (n = 0, one component); x = y and constant legs; dimension one (distinct points,
pairwise intersections empty); parallel walls; three concurrent lines in ℝ² (the bend avoids
the common point); a wall crossed once on each leg (uniqueness is per leg). All covered and
all provable from the node's proof.

Records and gates: node identical to side-live apart from `lean`; `lean.statement` verbatim
the file's signature; only stmt_dep `def-weil-vector-space-dimension` (`Module.finrank`), and
no DAG node owns `Convex`, `segment`, `Path`, `AffineSubspace`, `SOppSide`, `SSameSide` or
`connectedComponentIn` (searched the side-live `dag/nodes` declarations). Proof-dependency
modules are plain imports. Module and declaration docstrings carry the source place and
`(blueprint: lem-sfb-arrangement-generic-broken-line)`; the declaration docstring gives all
seven proof steps. Only `sorry`; no definition, no stronger assumption, no pro-étale content.

Searches: side-live DAG titles/declarations for hyperplane, convex, segment, connected
component, affine subspace; Mathlib `Analysis/Convex/PathConnected.lean`, `Side.lean`. No
existing statement of this result.

Mismatches found: none in the mathematics or the records. Only this section was rewritten.
