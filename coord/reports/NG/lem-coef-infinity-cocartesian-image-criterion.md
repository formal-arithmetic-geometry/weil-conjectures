## Worker report

The module `Sheaf.CategoryTheory.InfinityCocartesianImageCriterion` states
`SSet.Enhanced.infinity_cocartesian_image_criterion` with proof `sorry`. It binds
three small quasicategories `E`, `F`, and `B`, inner fibrations `p` and `q`, a
fully faithful simplicial functor `T`, and the equality `T ≫ q = p`. It then binds
the source and target vertices of an edge `e`, assumes that `e` is
`p`-cocartesian, and quantifies over every test vertex `z`.

For each `z`, the theorem renders the four clauses of the node as follows.

- `u` is the right-pinched arrow-space representative of `e`; the equality
  `arrowMappingSpaceInclusion ... u = diagramVertex e` fixes it to the displayed
  edge rather than an unrelated representative.
- `gE` is the map between the two canonical cocartesian precomposition roofs.
  Its displayed equation with the two roof inclusions is the complete coherent
  square commutation datum induced by `p`, including the whole triangle map.
- `IsHomotopyPullbackSquare` on `cocartesianPrecomposition`, `gE`,
  `arrowSpaceMap p`, and the base precomposition map is the homotopy-pullback
  criterion square for `e` at `z`.
- `gF` is the corresponding roof map for `T(e)` at `Tz`. The two existential
  `KanSquarePresentation` records retain both square triangles and the specified
  endpoint path. `AreNaturallyEquivalent PE.square PF.square` is the equivalence
  of the complete coherent square diagrams. The final
  `IsHomotopyPullbackSquare` is the image square at `Tz`, which is the asserted
  “in particular” clause.

The statement keeps only image tests `Tz`; it does not quantify over vertices of
`F` outside the image and does not assume essential surjectivity. Empty mapping
spaces and degenerate edges remain allowed by the simplicial-set predicates.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsFullyFaithful`,
  `diagramVertex`, `AreNaturallyEquivalent`, `mappingSpace`, and the coherent
  functor primitives.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` and
  `Sheaf.CategoryTheory.InfinityFibrations`: `InnerFibration` and
  `IsCocartesianEdge`.
- `Sheaf.CategoryTheory.InfinityCocartesianMappingCriterion`:
  `cocartesianPrecompositionSource`, `cocartesianPrecompositionInclusion`,
  `cocartesianPrecomposition`, `arrowMappingSpace`, `arrowSpaceMap`,
  `IsHomotopyPullbackSquare`.
- `Sheaf.CategoryTheory.InfinityHomBifunctorFunctoriality`:
  `infinity_hom_bifunctor_functoriality` and the coherent Hom comparison
  interface used by the proof.
- `Sheaf.CategoryTheory.PointwiseEquivalences`: `pointwise_equivalences`.
- `Sheaf.CategoryTheory.KanNervePullbackRecognition`:
  `KanSquarePresentation`, `kan_nerve_pullback_recognition`, and whole-square
  pullback invariance.
- `Sheaf.CategoryTheory.FixedEdgePrismCoherence`:
  `fixedEdgeSpace`, `FixedEdgePrismData`, and
  `fixed_edge_prism_coherence`. The dependency had no recorded `lean` interface,
  so its node copy and the published module are included in this delivery with a
  note explaining the repair.

Searches made on 2026-10-17:

- `msearch.py ... leanfinder "fully faithful simplicial functor over a common
  base preserves cocartesian mapping square"`: ordinary-category hits such as
  `CategoryTheory.Functor.IsCocartesian.map`; no quasicategorical coherent-square
  theorem.
- `msearch.py ... loogle "IsHomotopyPullbackSquare AreNaturallyEquivalent"`: zero
  hits; `IsHomotopyPullbackSquare` is unknown to Loogle.
- `msearch.py ... grep "cocartesian.*mapping.*square|AreNaturallyEquivalent"
  CategoryTheory`: zero hits.
- The inherited stage-1 searches also checked LeanFinder, Loogle, and Mathlib grep
  for fully faithful image tests and coherent homotopy-pullback squares; they found
  only ordinary-category analogues.

Edge cases checked before writing were `T = 𝟙`, `p = q`, `B = Δ[0]`, a degenerate
edge, empty mapping spaces, and a test vertex outside the image (which is
intentionally not quantified). The source and node statement agree clause by
clause; no statement correction or `STATEMENT-DISPUTED` flag is needed.

## Dependency modules

- `lem-coef-infinity-fixed-edge-prism-coherence`: the base node had no `lean`
  record even though the published `Sheaf.CategoryTheory.FixedEdgePrismCoherence`
  module now supplies its exact fixed-edge space, prism, roof, and naturality
  theorem. I copied that module into this delivery and recorded
  `SSet.Enhanced.fixed_edge_prism_coherence`; the copied node is changed only in
  its `lean` field, with this repair note.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
