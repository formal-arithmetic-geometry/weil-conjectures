## Worker report

The module `lean/Sheaf/AlgebraicTopology/CofibrantLocalizationDiagonalNerve.lean` states
`SSet.Bergner.cofibrant_localization_diagonal_nerve`. It uses the fixed-object category
`SSet.Bergner.Fixed O`. The two cofibrancy hypotheses are rendered by
`fixedCofibrations O (discreteInclusion V)` and
`fixedCofibrations O (discreteInclusion B)`, and the hypothesis that `v` is a cofibration is
`fixedCofibrations O v`. These are the recorded lifting-property definitions for mappingwise
trivial Kan fibrations.

The source's degreewise groupoid completion is represented by the existing
`SSet.Bergner.DegreewiseGroupoidCompletion V` interface from
`lem-coef-cofibrant-homotopy-groupoid-completion`. Its `target` is the fixed-object completion
`G(V)` and its `unit` is the canonical object-preserving map with the strict degreewise
localization universal property. This is the canonical formal adjoining of inverses; the
statement quantifies over every universal-property realization, which has the same induced
pushout map by uniqueness. The pushout `B[V^{-1}]` is rendered by
`P : Fixed O`, `i : B ⟶ P`, `j : C.target ⟶ P`, the compatibility equation
`hcompat : v ≫ i = C.unit ≫ j`, and
`hpush : IsColimit (PushoutCocone.mk i j hcompat)`. The conclusion is exactly the canonical
classifying diagonal nerve map
`CategoryTheory.CoherentNerve.diagonalNerveMap (bundleMap i)` being
`SSet.Enhanced.IsWeakHomotopyEquivalence`.

Every clause of the source statement is represented as follows:

- “small set `O`” is the explicit universe-bounded binder `{O : Type u}`.
- “fixed-object simplicial categories and functors” are `V B : Fixed O` and `v : V ⟶ B`.
- “cofibrant `V` and `B`” are `hV` and `hB` as the two displayed `fixedCofibrations` predicates.
- “`v` is a cofibration” is `hv : fixedCofibrations O v`.
- “groupoid-complete degreewise `V`” is `C : DegreewiseGroupoidCompletion V`, whose
  `unit` has `IsDegreewiseLocalization ... (fun _ => ⊤)` in every simplicial degree.
- “ordinary pushout in fixed-object simplicial categories” is the `PushoutCocone` colimit
  `hpush`, with `hcompat` supplying its span commutativity.
- “`B(T)_{p,q}`” and the simultaneous simplicial operators are the existing
  `CategoryTheory.CoherentNerve.diagonalNerve` construction; its map is
  `diagonalNerveMap (bundleMap i)`, so `p = 0` and empty products use the library's exact
  nerve conventions.
- “weak homotopy equivalence” is the exact predicate
  `SSet.Enhanced.IsWeakHomotopyEquivalence` from the Kan--Quillen dependency.
- No invertibility, Kan, connectedness, or nonemptiness hypothesis is added.

The theorem docstring records all twelve proof steps from the DAG: the sorted-model free
pair retract; the degreewise signed-word presentation and unique reduction; the comma-tree
calculation; finite-tree contraction; filtered colimits; the aspherical nerve criterion;
the degreewise pushout and bisimplicial diagonal argument; functoriality; and retract closure.
The only postponed proof is the theorem itself (`sorry`). No definition in this module uses
`sorry`.

Dependency declarations used:

- `Sheaf.AlgebraicTopology.SortedSimplicialAlgebraModel`,
  `AlgebraicTopology.sorted_simplicial_algebra_model` (the fixed-object sorted model and its
  boundary/horn lifting classes used by the cofibrancy predicates and proof plan).
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `SSet.KanQuillen.right_proper_kan_quillen` (the simplicial-set weak-equivalence and Kan
  model conventions used by the statement and proof plan).
- `Sheaf.AlgebraicTopology.CofibrantHomotopyGroupoidCompletion`,
  `SSet.Bergner.DegreewiseGroupoidCompletion` (the exact degreewise formal groupoid-completion
  interface needed for `G(V)`, added to `stmt_deps` in the sandbox node copy).
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting` supplies `Fixed`,
  `fixedCofibrations`, `discreteInclusion`, and `bundleMap`.
- `Sheaf.CategoryTheory.DiagonalCoherentNerveComparison` supplies
  `CategoryTheory.CoherentNerve.diagonalNerveMap`.

The proof-only imports are retained as required by the stage-2 contract:
`BisimplicialDiagonalEquivalence`, `GrothendieckAsphericalBaseChange`,
`NerveNaturalHomotopyEquivalence`, and `SSetGluingFilteredEquivalences`.

Edge cases checked against the source statement and proof are the empty object set `O`,
zero nerve degree `p = 0`, empty products, loops and parallel generating arrows, an empty
marked subgraph, the case where every arrow is marked, isolated vertices, absent mapping
simplices, and disconnected components. The formal statement adds no Kan, connectedness,
nonemptiness, or component-invertibility assumptions.

Searches made:

- `msearch.py ... leanfinder "degreewise partial inversion of a cofibrant fixed-object
  simplicial category preserves the diagonal nerve"`: only ordinary nerve/standard-simplex
  and homotopy-category results; no matching theorem.
- `msearch.py ... loogle "CategoryTheory.FreeGroupoid,
  CategoryTheory.CoherentNerve.diagonalNerveMap"`: no hits (the combined identifier is not a
  Loogle name).
- `msearch.py ... grep "localiz.*nerve|nerve.*localiz|partial.inversion"
  CategoryTheory`: no hits.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` for partial-inversion,
  localization-diagonal-nerve, and cofibrant-localization-nerve: no exact target declaration.
  The existing completion interface and diagonal nerve infrastructure were found and reused.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
