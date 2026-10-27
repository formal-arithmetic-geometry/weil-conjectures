## Worker report

The module `Sheaf.Topology.ActionClopenOrbitRefinement` states
`MulAction.exists_openNormalSubgroup_finite_clopen_orbit_refinement` with proof `sorry`.
No definitions, auxiliary theorems, new nodes, dependency repairs, or statement corrections
are needed. The original node is changed only in `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The size convention is implemented by explicit universe levels `u v`, with `G : Type u`
  and `P : Type v`. No site, skeleton, or derived category occurs in this statement.
- A compact Hausdorff topological group is `[Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]`.
- The open normal subgroup basis is the hypothesis
  `hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ U`.
  This quantifies over every neighborhood, including neighborhoods not themselves open.
- A compact topological space is `P : Type v` with `[TopologicalSpace P] [CompactSpace P]`.
  No separation or nonemptiness assumption is added for P.
- The continuous left action is `[MulAction G P] [ContinuousSMul G P]`; the latter means
  joint continuity of `(g,p) ↦ g • p`.
- The finite set of blocks is `α : Set (Set P)` with `hfinite : α.Finite`.
  `hpartition : Setoid.IsPartition α` means that the empty set is not a block and each
  point belongs to exactly one block. This is equivalent to nonempty pairwise disjoint
  blocks covering P. `hclopen : ∀ A ∈ α, IsClopen A` adds precisely openness and closedness.
- The first conclusion is an existential `N : OpenNormalSubgroup G` with
  `∀ n ∈ N, ∀ A ∈ α, (fun p : P ↦ n • p) '' A = A`, exactly blockwise stabilization.
- The orbit T is fixed by equality to `Set.range` of the image of α under block translation.
  The next conjunct `T.Finite` states finiteness of that entire orbit.
- The equality defining β uses `B.Nonempty` and a function `f : T → Set P` whose value
  belongs to each partition `γ.val`, with `B = ⋂ γ : T, f γ`. Thus it is precisely the
  collection of all nonempty intersections of one chosen block from every member of T.
  Its equality fixes β, rather than merely requesting some invariant refinement.
- `β.Finite`, `Setoid.IsPartition β`, and `∀ B ∈ β, IsClopen B` state that this exact
  collection is a finite clopen partition with nonempty blocks.
- `∀ B ∈ β, ∃ A ∈ α, B ⊆ A` is refinement of α.
- `∀ g : G, (fun B : Set P ↦ (fun p : P ↦ g • p) '' B) '' β = β` says that G permutes
  the blocks. Group inverses make these translations bijective, so equality of the
  block collections gives precisely permutations, without adding a chosen enumeration.

Dependencies and source declarations read:

- `def-weil-size-convention` has an existing convention record with no declaration/module;
  its note directs citers to state universe levels explicitly, as done here.
- `Mathlib.Data.Setoid.Partition`, `Setoid.IsPartition` (line 193), including its full
  definition and the nonemptiness, disjointness, and covering lemmas immediately below.
- `Mathlib.Topology.Algebra.OpenSubgroup`, `OpenNormalSubgroup` (line 368), extending
  `OpenSubgroup` with normality of its underlying subgroup.
- `Mathlib.Topology.Algebra.MulAction`, `ContinuousSMul`, using Mathlib's continuous
  left-action interface. No private action or partition notion is introduced.
- Both proof dependencies are Mathlib leaves in
  `Mathlib.Topology.Compactness.Compact`: `IsClosed.isCompact` and
  `generalized_tube_lemma`. Their signatures were read in full, and this module is
  imported publicly because its compactness interface is also used by the statement.
  The theorem docstring records all six proof steps and identifies both leaves.
- The local PDF was read at page 28, Example 4.1.10. Its pro-objects in finite discrete
  G-sets provide the source context; the node explicitly supplies the general compact-P
  invariant-refinement expansion. No profiniteness assumption on P is inserted.

Edge cases checked before writing:

- P empty: `Setoid.IsPartition α` forces α empty. The orbit is the singleton containing
  the empty partition. A block choice from that member is impossible, so β is empty.
  This empty β satisfies `Setoid.IsPartition`; N can be the whole group.
- P nonempty with α = {P}: T = {α} and β = {P}; the whole group stabilizes each block.
- Trivial G: T is the singleton {α}, and β is α.
- Indiscrete, non-Hausdorff compact P: its only partition when nonempty is {P}; accepted.
- Finite discrete P: translating and intersecting blocks gives the familiar invariant
  finite partition. Duplicate intersections are harmless because β is a set.
- T is never empty, because G contains 1. The formula therefore does not accidentally
  create a block P from an empty-index intersection in the empty-space case.

Searches actually run (through the prescribed msearch wrapper unless identified as rg):

- LeanFinder: “A compact group acting continuously on a compact space has finite orbit
  on finite clopen partitions and an invariant common refinement”: eight hits, including
  `CategoryTheory.PreGaloisCategory.has_decomp_quotients`,
  `exists_clopen_partition_of_clopen_cover`, `IsCompact.exists_finite_cover_smul`, and
  properly discontinuous/minimal-action statements. None states this theorem: the
  clopen-cover result has stronger space hypotheses and no group invariance; the others
  concern discrete finite actions or different hypotheses/conclusions.
- Loogle: `ContinuousSMul, IsClopen`: zero hits (run twice, same result).
- Mathlib grep: `invariant.*(clopen|partition|DiscreteQuotient)|`
  `(clopen|partition|DiscreteQuotient).*invariant`: zero hits.
- LeanSearch: “A compact group acting on a compact space has finite orbits on finite
  clopen partitions and an invariant clopen refinement”: eight hits. These include the
  same clopen-cover result, quotient finiteness for open subgroups, and the fact that
  orbits themselves partition a set. None gives the requested translated-partition orbit
  or the specified common refinement.
- rg over both `lean/WeilConjectures` and `lean/Sheaf` for
  `clopen.*(partition|refin)|partition.*clopen|clopen.*orbit|orbit.*clopen` found related
  constructions but no exact statement. In particular
  `WeilConjectures.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition` addresses
  scheme base changes and a special nontrivial partition; its source was opened and
  is not this general continuous group action theorem.
- rg for `lem-sfb-action-clopen-orbit-refinement` in `lean/WeilConjectures` found no match.
  rg for the proposed declaration name across both Lean trees and
  `dag/lean_names_upstream.json` also found no match.
- Mathlib rg for partition definitions found `Setoid.IsPartition`, `Finpartition`, and
  `Partition`; the first directly models this node's set of nonempty blocks, so it is
  used with finiteness and clopenness as separate hypotheses. `DiscreteQuotient` and
  the existing partition-restriction module were also read; no second notion is defined.

Validation: the prescribed scompile.py compiled both sandbox and library module modes
cleanly. The sole theorem has the required `sorry`; no diagnostic commands remain.

## Second reading by Q145

Author's second reading, with the original node and completed Lean file open; independent
review is left to the maintainer as prescribed by the dispatcher brief. I checked the
group hypotheses, neighborhood basis, compact P, and joint left action against their
binders. I unfolded `Setoid.IsPartition` and checked its exact empty-space behavior;
finiteness and clopenness are separate explicit hypotheses. I checked image-of-image
in the T equation is gα, and that the β equation quantifies over every γ in that exact
orbit, requires one member block, and removes exactly the empty intersections. The final
conjuncts supply finiteness, partition, clopenness, refinement, and permutation of that
same β. No clause is missing, no additional mathematical hypothesis is present, and no
mismatch required a statement change. No statements are disputed.
