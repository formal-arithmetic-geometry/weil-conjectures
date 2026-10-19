## Worker report

The module `Sheaf.CategoryTheory.InfinityCartesianMappingCriterion` states
`SSet.Enhanced.infinity_cartesian_mapping_criterion` with proof `sorry`. It uses the
path-space homotopy-pullback predicate `IsHomotopyPullbackSquare`, the right-pinched
mapping spaces and `mappingSpaceMap`, and the canonical postcomposition map supplied by
`canonicalPostcompositionMap`.

The hypotheses are rendered as follows. `E B : SSet.{u}` are the two quasicategories;
`[Quasicategory E]` and `[Quasicategory B]` are their quasicategory structures; `p : E ⟶ B`
is the simplicial map; `_hp : InnerFibration p` is the inner-fibration hypothesis;
`x y : E _⦋0⦌` are the source and target vertices; `s : Δ[1] ⟶ E` is the specified
edge; `_hsx : E.δ 1 (SSet.yonedaEquiv s) = x` and `_hsy : E.δ 0
(SSet.yonedaEquiv s) = y` fix its endpoints. The conclusion's left clause is
`IsCartesianEdge p s`, exactly the final-horn lifting predicate. Its right clause
quantifies over every `z : E _⦋0⦌` and asserts
`IsHomotopyPullbackSquare` for the square whose top map is
`canonicalPostcompositionMap (C := E) z x y ...`, whose two vertical maps are
`mappingSpaceMap p z x` and `mappingSpaceMap p z y`, and whose bottom map is the analogous
`canonicalPostcompositionMap (C := B) ...` for the image edge. The two endpoint proofs for
`p(s)` are derived only by naturality of `p` and the supplied `_hsx`, `_hsy`. Thus the
statement has no Cartesian-fibration or other-lift existence assumption.

The dependency declarations used are:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations
  `SSet.Enhanced.mappingSpace`, `SSet.Enhanced.mappingSpaceMap`, and
  `SSet.Enhanced.IsWeakHomotopyEquivalence`.
* `Sheaf.CategoryTheory.InfinityFibrations`, declaration
  `SSet.Enhanced.IsCartesianEdge`.
* `Sheaf.CategoryTheory.InfinityMappingComposition`, theorem
  `SSet.Enhanced.mapping_composition` (the canonical composition package).
* `Sheaf.CategoryTheory.RelativeInfinityCone`, declaration
  `SSet.Enhanced.IsHomotopyPullbackSquare`.
* `Sheaf.CategoryTheory.InfinityReflectionAssembly`, declaration
  `SSet.Enhanced.canonicalPostcompositionMap` (a recorded helper determined by
  `mapping_composition`).

Edge cases checked: `z` is unrestricted, including vertices with empty mapping spaces;
`E` or `B` may be empty when the displayed binders are inhabited; `s` may be degenerate;
`p` may be an identity or map to a terminal simplicial set; no Cartesian lift besides
`s` is required; and the single universe `u` is shared by all simplicial sets and maps.
The endpoint transport for `p(s)` uses no universe restriction or choice.

Searches for an existing statement or definition were made before writing:

* `msearch.py Q59 lem-coef-infinity-cartesian-mapping-criterion leanfinder` with the
  query “For an inner fibration of quasicategories, an edge is Cartesian iff
  postcomposition induces homotopy pullback mapping space squares”: only ordinary
  categorical-fibration results, no match.
* `msearch.py ... loogle "IsCartesian homotopy pullback Map"`: zero hits.
* `msearch.py ... grep "cartesian.*mapping|mapping.*cartesian" Mathlib/AlgebraicTopology/Quasicategory/`:
  no match.
* `msearch.py ... leansearch` for the horn-lifting/mapping-space equivalence: only
  ordinary-category results, no quasicategorical match (one request reported the
  documented service rate limit).
* `rg` over `WeilConjectures/`, `lean/Sheaf/`, and `Mathlib` for Cartesian mapping
  criteria: no existing theorem with this statement. The existing cocartesian criterion
  is the opposite-direction theorem and does not state the present postcomposition
  square.

The file was compiled with
`scompile.py Q59 lem-coef-infinity-cartesian-mapping-criterion` and completed with no
errors or warnings. The only postponed proof is the theorem proof itself.

## Second reading by Q59

I reread the node and the module clause by clause. The edge endpoints use `δ 1` and
`δ 0` exactly as in the node. The square has `Map_E(z,x)` and `Map_E(z,y)` on top,
`Map_B(pz,px)` and `Map_B(pz,py)` below, with both horizontal arrows represented by the
canonical postcomposition maps. The vertical maps are the actual simplicial maps induced
by `p`. The homotopy-pullback predicate is the project's path-space predicate, so it
includes the canonical comparison and weak-homotopy-equivalence condition from the node.
The naturality calculations for the image edge preserve both endpoint equations. No
hypothesis was added, no conclusion clause was dropped, and no other Cartesian lift was
introduced. The module and its node record agree on the declaration and signature.

## Maintainer review fix (2026-10-17)

The delivered right-hand side used `canonicalPostcompositionMap` for `E` and for `B`. Each is
an independent `Classical.choose` of a composition representative that
`mapping_composition` fixes only up to homotopy. `IsHomotopyPullbackSquare` needs the
square to commute strictly, so the delivered clause could fail for a Cartesian edge (for
example, every edge is Cartesian for an automorphism `p`, but strict `p`-equivariance of the
chosen composition is not derivable). The fix presents the square by its canonical
fixed-second-edge triangle roofs (`cartesianPostcompositionSource`, `...Inclusion`,
`cartesianPostcomposition`). These are the slice representative of the node's Steps 8–9 and
the exact dual of the landed `infinity_cocartesian_mapping_criterion`. The left vertical map
is fixed by the ambient triangle inclusion, so the commutation witness is the canonical
strict one. The hypotheses are unchanged.
