## Worker report

The module `Sheaf.CategoryTheory.LocalizationFilteredColimit` states
`SSet.Enhanced.isLocalizationAtEdges_colimMap_of_isFiltered`, with the sole theorem
proof `sorry`. It defines no new notion. The item node changes only in `lean`.
No statement correction, disputed statement, new node or dependency repair is needed.

I read the item's statement, four proof steps and dependency records, the recorded
localization and enhanced-category source declarations, and Kerodon Corollary
the project server (https://kerodon.net/tag/05ZQ), retrieved online on 2026-10-17. The source
allows arbitrary simplicial sets and arbitrary transition maps, exactly as the node.

Hypothesis and conclusion correspondence:

- Small nonempty ordinary category with cocones for every finite diagram:
  `(I : Type u) [SmallCategory I] [IsFiltered I]`. Mathlib's `IsFiltered` includes
  nonemptiness, common targets for pairs of objects, and equalization of parallel
  arrows. These are equivalent to the node's finite-diagram cocone condition.
  In particular, the empty finite diagram is included. Mathlib's
  `CategoryTheory.IsFiltered.cocone_nonempty` implements the forward direction.
- Strict diagram of maps of small simplicial sets:
  `(X Y : I ⥤ SSet.{u}) (p : X ⟶ Y)`. The functor laws supply strict identities
  and compositions; `p.naturality` supplies each square
  `X.map a ≫ p.app j = p.app i ≫ Y.map a`.
- Collections of edges: `(V : ∀ i : I, Set ((X.obj i) _⦋1⦌))`.
- Preservation of edges by every transition: `hV` states
  `(X.map a).app (Opposite.op ⦋1⦌) '' V i ⊆ V j` for every arrow `a`.
  This is set-image containment, with no injectivity or surjectivity requirement.
- Every stage is a localization at precisely `V i`: `hp` states
  `∀ i, IsLocalizationAtEdges.{u, v} (p.app i) (V i)`.
  The dependency quantifies over all test quasicategories in `max u v` and requires
  the specified precomposition to factor through and be a coherent equivalence
  onto the full subcategory of edge-inverting diagrams. Neither endpoint needs
  to be a quasicategory.
- Degreewise colimits `X,Y` and the induced map: `colimit X`, `colimit Y`, and
  `colimMap p`. Mathlib simplicial sets are presheaves, whose colimits are
  computed pointwise. `colimit.ι X i` is the specified stage map `j_i`;
  `CategoryTheory.Limits.ι_colimMap` supplies its compatibility with `p.app i`.
- The exact edge collection `V = ⋃ i, j_i(V_i)` is written directly as
  `⋃ i : I, (colimit.ι X i).app (Opposite.op ⦋1⦌) '' V i`.
- Conclusion: `IsLocalizationAtEdges.{u, v} (colimMap p)` at exactly this union.
  No quasi-category or transition-monomorphism assumption has been introduced.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge`, `fullSubcomplex`, `IsFunctorEquivalence`,
  used through the recorded localization definition. Its full signatures and
  docstrings were read; no private version is introduced.
- `Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap`:
  `SSet.Enhanced.IsLocalizationAtEdges` and its underlying
  `edgeInvertingDiagrams`. I read the full module, including its degreewise
  universe lift and its factorization equation.
- Proof-only imports:
  `Sheaf.AlgebraicTopology.JoyalFilteredEquivalences`, declaration
  `SSet.categorical_equivalences_colimMap_of_isFiltered`; and
  `Sheaf.AlgebraicTopology.JoyalFunctorEquivalenceTest`, declaration
  `SSet.joyal_functor_equivalence_test`. Their complete recorded signatures and
  source docstrings were read. They require no extra hypothesis in this theorem.
- `lem-coef-simplicial-localization-existence` has no Lean record or Mathlib match
  at this base. It supplies only a future proof step, not an object needed to
  type the current statement, so it has no import yet. Its entire four-step use
  remains in the theorem docstring. No construction from it is duplicated.
- Mathlib's `CategoryTheory.IsFiltered`, ordinary functors/natural transformations,
  presheaf colimits, `colimMap` and `colimit.ι` supply the remaining constructions.

Edge cases checked against the statement before writing: a singleton indexing
category recovers the stage property; empty distinguished edge collections give
an empty union; empty simplicial sets are allowed, including entirely empty
source and target diagrams; degree-one maps may identify distinguished edges
or send them to degenerate edges; parallel indexing arrows are permitted;
noninjective transitions are unrestricted. An empty index category is excluded
exactly by the node's nonemptiness hypothesis. Universes `u,v` are explicitly
bound: the small indexing category and simplicial sets share `u` as required by
the project size convention, while tests can be in every enlargement `max u v`.
No variable or universe is auto-bound.

Searches for reuse (all run with the prescribed `msearch.py`, with raw output in
`searches.jsonl`):

- LeanFinder: `Filtered colimits preserve localization of simplicial sets at
  compatible collections of edges`. Eight hits, including
  `SSet.instIsStableUnderFilteredColimitsMonomorphisms`, `SSet.hasColimits`,
  regular epimorphisms and finite presentability. None states edge localization
  stability; the first preserves monomorphisms rather than the localization
  universal property.
- Loogle: `"SSet", "IsFiltered", "Localization"`: zero hits.
- Mathlib grep: `[Ll]ocaliz.*[Ff]iltered|[Ff]iltered.*[Ll]ocaliz`: zero hits.
- LeanSearch: `Filtered colimits preserve localization of simplicial sets at
  collections of edges`: eight hits, on orthogonal local objects, commuting
  filtered colimits and finite limits, preservation of filtered colimits and
  localization of modules. No match. Ordinary categorical localization's
  `Functor.IsLocalization` in Mathlib `CategoryTheory/Localization/Predicate.lean`
  was also read: it concerns ordinary functor categories, not coherent simplicial
  functor categories at specified edges.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` for
  `localization.*[Cc]olimit|[Cc]olimit.*[Ll]ocalization|IsLocalizationAtEdges|lem-coef-localization-filtered-colimit`:
  unrelated ring/sheaf localizations, the existing localization definition, and
  the downstream `UniversalLocalizationDegenerateEdges` proof-plan mention;
  no theorem already stating this result.
- `rg` for `IsLocalizationAtEdges|05ZQ|localization_filtered_colimit` in
  `dag/lean_names_upstream.json`, upstream and the side CategoryTheory modules:
  only the existing localization definition. No upstream attachment matches.

Validation: the prescribed `scompile.py Q02 lem-coef-localization-filtered-colimit`
compiled the sandbox file and the library-path copy cleanly, each in 1.2 seconds.
The initial elaboration exposed an ambiguity in `.app _⦋1⦌`; using the explicit
object `.app (Opposite.op ⦋1⦌)` fixed it without changing the statement.

## Second reading by Q02

This is the worker's self-check for direct delivery; independent review belongs
to the maintainer. I reopened the node and Lean file and compared every clause.
The small/nonempty/finite-cocone condition is exactly `SmallCategory` plus
`IsFiltered`; functor laws and naturality account for every strict-diagram law.
The edge sets and their transition-image containment use actual degree-one
simplices. `hp` uses the recorded coherent localization definition rather than
ordinary localization or a restriction to quasicategories. The conclusion is
about the canonical colimit map and the literal union of the colimit-leg images.
The independent test universe remains present in both premise and conclusion.
Empty shapes within the diagram and empty edge sets remain allowed. No
hypothesis, conclusion clause, stronger fibrancy condition or edge-injectivity
condition is missing or added. The only change from the first draft was the
explicit degree-one object needed for elaboration. I checked that all four
DAG proof steps are retained in the declaration docstring, that the two stated
proof dependencies are imported privately, and that the unstated proof-only
localization-existence node is listed above rather than restated.
