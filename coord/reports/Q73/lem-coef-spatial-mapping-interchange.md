## Worker report

`Sheaf.CategoryTheory.SpatialMappingInterchange` states
`SSet.Enhanced.spatial_mapping_interchange`, in the recorded right-pinched mapping-space
and coherent-nerve conventions. Definitions contain actual simplicial maps and records;
the main theorem and six structural endpoint identities have `sorry` proofs with source
and natural-language proof docstrings. The helper identities are normalization parts of
this node, not independent mathematical assertions. All declarations are listed in
`lean.declarations`.

The saved packet was retained and its prescribed first dry run was run. It compiled,
but preflight rejected the recorded signature's trailing `:=`; the record now matches
the signature as read by preflight. Self-review also found that the saved evaluation
predicate was a reflexive equality and its naturality predicate ended in `True`. Those
predicates were replaced by actual whole-space evaluation homotopies and coherent
comparison squares. The universal preliminary local-smallness quantifier, previously
restricted to two fixed shapes, was restored. These repair the Lean rendering; the
natural-language node statement, proof, and proof dependencies are unchanged.

Clause-by-clause correspondence:

* Universes: `u` is the small-space universe. `homSpaceCategory.{u,v}` is the recorded
  coherent nerve of small Kan complexes lifted to `max (u+1) v`. `spatialShape` applies
  the matching lift to a small shape; `spatialDiagrams` is its actual internal Hom.
  `z` is independently bound for further containing-universe parameters. No equality
  between the small and containing universes is imposed.
* Every small quasicategory: `models : ∀ (M : SSet.{u}) [Quasicategory M],
  SpatialHomModel (spatialDiagrams M)` precedes all input diagrams. Each model contains
  its quasicategory structure and the dependency's `HomBifunctorData`. Its
  `valueComparison` is a weak equivalence to a lifted small Kan complex; its specified
  homotopy inverse is also retained. `bimodels` does the same for the actual product
  shape, avoiding an unjustified identification between a lifted product and a product
  of lifts. `mS` is the ambient-space Hom model.
* The small quasicategories `K,L` and coherent diagrams: `comparisons` quantifies
  `K,L : SSet.{u}` with their `Quasicategory` instances. The record
  `SpatialInterchangeAtShapes` quantifies every vertex `f`, `q`, `w` of the three
  internal functor objects. Such vertices are exactly coherent simplicial maps, by
  the dependency's `diagramVertex` and the internal-Hom unit adjunction. Neither
  ordinary nerves nor only ordinary functors replace those objects.
* Transposition of W: `spatialRows` is the closed curry of the universal evaluation
  map. `spatialOppositeRows` takes its opposite and the canonical double-opposite
  isomorphism. `spatialRFamily` pairs this map with Q and composes with the chosen
  Hom bifunctor on `Fun(L,S)`. It gives both the values and all higher actions of
  R_Q. `spatialR` extracts its vertex for `(q,w)`.
* Pointwise T: `spatialTFamily` evaluates F and Q with their common simplex parameter,
  takes the opposite first action, and composes with the ambient Hom bifunctor.
  `spatialT` extracts its vertex. `spatialR_at`, `spatialT_at`, and `spatialRow_at`
  explicitly identify the endpoint values used in the mapping-space comparisons.
* Whole mapping-space equivalence: `spatialLeft mL f q w` and
  `spatialRight mS f q w` are the exact two right-pinched mapping spaces in the node.
  `SpatialInterchangeAtShapes.comparison` is a simplicial map between them; `weak`
  asserts `IsWeakHomotopyEquivalence`, and `inverse` retains a two-sided simplicial
  homotopy inverse. No point or mere component-set bijection substitutes for this.
* Specified evaluation: `spatialAlphaAt` and `spatialTauAt` use the recorded
  `mappingSpaceMap` of the actual evaluation functors, followed only by endpoint
  transports proved in the structural identities. `spatialEvaluateAlpha` evaluates
  alpha_k on x, decodes the Hom_L value using the specified inverse comparison,
  restricts at l, and evaluates on w. `spatialEvaluateTau` evaluates tau_(k,l) on w,
  decodes the spatial Hom value, and evaluates on x. `evaluationFormula` is a
  `SSet.Homotopy` between these two actual maps on
  `(spatialLeft ⊗ spatialValue F(k)) ⊗ spatialValue W(k,l)`.
  It is thus an identity of coherent evaluations, with every simplex parameter
  retained, rather than an equality on vertices or a reflexive predicate.
* The normalized spatial decoder is tied to
  `CategoryTheory.Spaces.PointFamily.ComparisonData` and its actual maximum-
  augmentation map `alpha`. `spatialEnrichedAlpha` only lifts that map and transports
  its endpoints using `spatialKan_vertex`. The decoder contains actual homotopy
  inverses of this specified map. It is not an arbitrary equivalence or evaluation.
  The main theorem outputs p, its weak-augmentation property, c, and d; none is an
  additional hypothesis on the input diagrams or an existence-based definition.
* Coherent naturality in F,Q,W: `spatialParameters` is
  `Fun(K,S).op × (Fun(L,S) × Fun(K.op×L,S).op)`. The maps `spatialLeftFamily` and
  `spatialRightFamily` are the actual coherent Hom composites on that whole object.
  `naturalEdge`, `naturalSource`, `naturalTarget`, and `naturalEquivalence` give an
  equivalence in its entire internal functor quasicategory. `component` identifies
  its component edges with the raw comparison maps under their fixed value
  comparisons, by whole-space homotopies (`SpatialEdgeRepresents`).
* Restriction in K and L: the final universal quantifier ranges over every pair
  `a : K' ⟶ K`, `b : L' ⟶ L`, including identities. The restriction maps are the
  actual precomposition maps `spatialRestriction` and `spatialBiRestriction`.
  `SpatialInterchangeRestriction.rowEdge` is a coherent transformation from
  restricted R to the R of the restricted inputs; `rowNormalization` identifies
  every row component with `mappingSpaceMap (spatialRestriction b)` under the
  specified Hom comparisons. `leftNormalization` and `rightNormalization` tie
  the two functor-family edges to the actual raw restriction maps. `upper` and
  `lower` are two whole functor-category 2-simplices with common `diagonal` filling
  the naturality square; `square` also records its homotopy on raw mapping spaces.
* Additional simplicial parameters: `parameters` retains two-sided homotopy inverses
  after applying `(ihom P).map` to the lifted comparison for every
  `P : SSet.{max (max (u+1) v) z}`. Postcomposition of a P-family by the comparison
  is therefore an equivalence with its inverse homotopies. Restrictions P' -> P
  commute with those operations because these are actual internal-Hom maps.
  The whole-space evaluation homotopies and functor-family square likewise retain
  shared parameters by precomposition; they are not pointwise witnesses.
* Empty shapes and values: there is no inhabitance assumption on any shape, Kan
  value, or mapping space. Empty-shape internal functors are terminal; empty L makes
  each row Hom terminal, while empty K makes both transformation spaces terminal.
  The degreewise enriched evaluation and its prescribed comparison allow empty Kan
  values. No definition selects a vertex of a value or a mapping space. In particular
  E(empty,C) and E(empty,empty) are terminal; E(A,empty) may be empty for nonempty A.

Dependency interfaces read and used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.mappingSpace`, `mappingSpaceMap`, `diagramVertex`, `evaluation`,
  `IsWeakHomotopyEquivalence`, and `IsEquivalenceEdge`.
* `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.infinityCategory` and `Kan`; the ambient category is the
  coherent nerve with internal-Hom enrichment, not an ordinary category of spaces.
* `Sheaf.CategoryTheory.InfinityHomBifunctorFunctoriality`:
  `SSet.Enhanced.homSpaceCategory`, `HomBifunctorData`, `homValue`,
  `homSpaceEdgeSource`, `homSpaceEdgeTarget`, and `homSpaceEdgeTransport`.
  The model structure is passed explicitly to its projections, avoiding an extra
  global instance or an incompatible universe specialization.
* `Sheaf.CategoryTheory.PointFamilyQCounitIdentification`:
  `CategoryTheory.Spaces.PointFamily.ComparisonData` and its normalized `alpha`.
  This already-landed proof dependency is added to `stmt_deps`, because the actual
  counit-normalized decoder occurs in the statement. No dependency module is repaired.

The recorded proof-dependency modules
`EnhancedFunctorConeCalculus`, `KanCoherentNerveQuasicategory`,
`ParametricUniversalArrows`, and `TwistedArrowLeftFibration` are imported for stage 3.
`lem-coef-coherent-end-twisted-arrow-formula` has no recorded Lean module at the time of
this check, so no guessed proof-only import is supplied. The node's proof describes its
use explicitly; it is not needed to type the present statement.

Searches retained from the previous attempt (`searches.jsonl`) and checked:

* msearch grep `spatial.*interchange|interchange.*spatial|quasicategory` in
  `CategoryTheory/Enriched`: no hits.
* msearch loogle `CategoryTheory.MonoidalClosed.FunctorCategory.adj`: an ordinary
  functor-category adjunction, not the quasicategorical statement.
* msearch LeanFinder queries for coherent spatial mapping interchange: generic
  nerve and quasicategory results, no exact declaration.
* msearch LeanSearch queries for equivalences of coherent transformation mapping
  spaces: generic uniform-function/congruence results, no exact declaration.
* Additional loogle `"Quasicategory", "Hom"`: internal-Hom quasicategory instances,
  not the interchange theorem. Grep `interchange|currying|tensorHom` returns ordinary
  categorical currying, localization, and Day-convolution declarations.
* Resumption search, msearch loogle `SSet.Enhanced.spatial_mapping_interchange`:
  zero hits (unknown identifier). Direct rg over Mathlib, `WeilConjectures`, and
  project `lean/Sheaf` for the main and helper names found no existing declaration.
  Direct rg for this node id in `WeilConjectures` found no upstream implementation.

Source reread: https://kerodon.net/tag/03P7, Example the project server, computes whole
transformation spaces by the twisted-arrow end of Hom(G(X),G'(Y)). As the node's source
record says, the two-variable interchange is its transposition consequence, rather
than a verbatim quotation. The smallness source remains Cisinski 5.7.3 as recorded.
No natural-language statement correction, new definition node, or dependency-interface
repair was needed. All added declarations specify the existing interchange construction
and its endpoint/restriction normalizations in this owning module.

Validation: the full revised module compiled cleanly through `scompile.py`, separately
in sandbox and library-module layouts, with explicit universes and `autoImplicit false`.
Only the seven named stage-2 theorem proofs are postponed. The prescribed final dry run
and push are performed after updating the verbatim signature record.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
