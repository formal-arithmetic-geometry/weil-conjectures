## Worker report

The module `Sheaf.AlgebraicTopology.InverseGadgetCategoricalContractibility` states
`SSet.Enhanced.inverse_gadget_categorical_contractibility`. Its only theorem proof is
`sorry`; no definition, instance, or additional theorem is introduced.

Clause-by-clause match:

- Small simplicial sets and the coherent functor conventions are Mathlib `SSet`, `ihom`,
  and the recorded `SSet.Enhanced.IsFunctorEquivalence`, imported publicly from
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. The latter means a simplicial
  quasi-inverse and two coherent natural equivalences, each with inverse-triangle
  witnesses. It is the whole functor-category equivalence, including higher simplices.
- The specified quotient Q is the already landed
  `SSet.Enhanced.inverseTetrahedron.{u}` in
  `Sheaf.AlgebraicTopology.FiniteInverseTetrahedron`, owned by
  `lem-coef-finite-inverse-tetrahedron`. I read its declaration, both edge maps, the
  first pushout, and the quotient maps. The edge maps are `yonedaEquiv.symm` of
  `stdSimplex.edge 3 0 2` and `stdSimplex.edge 3 1 3`, respectively. Each pushout's
  other leg is `stdSimplex.isTerminalObj₀.from Δ[1]`, to its own copy of Δ[0].
  These successive presheaf pushouts are the node's simultaneous coproduct pushout:
  maps from either construction to any T are exactly a map Δ[3] → T and two maps
  Δ[0] → T, subject to the separate two edge-agreement equations. This equivalence
  of universal properties is degreewise and natural, so there is no different
  quotient or added identification. In particular its two point vertices remain
  distinct. No second definition of Q is written.
- The unique p : Q → Δ[0] is literally
  `stdSimplex.isTerminalObj₀.from inverseTetrahedron.{u}`. There is no arbitrary map
  or extra hypothesis about this map.
- Every quasicategory E is `(E : SSet.{max u v}) [Quasicategory E]`. Both universes
  are explicitly bound. The independent enlargement `v` is unrestricted;
  `uliftFunctor.{v,u}.map` transports the actual p degreewise to its test universe.
  Thus this includes all containing universes and the case v = 0.
- Restriction p* is exactly
  `(MonoidalClosed.pre (uliftFunctor.{v,u}.map p)).app E`. Its domain is
  `Fun(ulift Δ[0], E)`, canonically E, and its codomain is
  `Fun(ulift Q, E)`. This is the displayed functor in the node, with its stipulated
  universe enlargement. The conclusion is `IsFunctorEquivalence` of this specified
  map; no equivalence merely of cores, homotopy categories, or unbound maps replaces it.
- No `Quasicategory` or `KanComplex` hypothesis on Q occurs. No nonemptiness
  assumption on E occurs. The only instance binder is exactly `[Quasicategory E]`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsFunctorEquivalence`, `AreNaturallyEquivalent`,
  `IsEquivalenceEdge`; internal homs and the constant/evaluation conventions.
- `Sheaf.AlgebraicTopology.FiniteInverseTetrahedron`:
  `inverseTetrahedronEdge02`, `inverseTetrahedronEdge13`,
  `inverseTetrahedronFirst`, `inverseTetrahedronFirstMap`, `inverseTetrahedron`.
  Its already landed node is added to stmt_deps, as authorized by brief-stage2 §5.
  Its theorem is not assumed as a new hypothesis. The node's statement and its
  full recorded interface were read; its dependency closure does not reach this
  item (seven nodes visited), so this addition causes no dependency cycle.
- Proof-only imports follow the original DAG: UniversallyLocalizingSimplicialMap
  (`IsLocalizationAtEdges`), EnhancedFunctorConeCalculus
  (`enhanced_functor_cone_calculus`), InfinityMappingComposition
  (`mapping_composition`), PointwiseEquivalences (`pointwise_equivalences`), and
  JoyalFunctorEquivalenceTest (`SSet.joyal_functor_equivalence_test`). Their recorded
  signatures were read. The original proof dependency
  `lem-coef-localization-monomorphic-pushout` has no Lean record or module at this
  reading, so there is no import for it yet; it is only a postponed-proof dependency
  and its statement is not needed to type this item. No dependency module is needed.

Edge cases checked before writing:

- E empty: Q and Δ[0] both have vertices, so both entire functor simplicial sets
  into E are empty. The required equivalence is between empty simplicial sets;
  no dimension-zero horn condition or object choice excludes this case.
- E terminal: both functor simplicial sets are terminal, with the unique restriction.
- E the nerve of an ordinary category: a Q-diagram gives arrows f,g,h with gf and
  hg identities after collapse. The two-out-of-six calculation forces every edge
  invertible. The resulting diagram category is equivalent to the target category,
  consistent with the stronger coherent assertion, without relying on a core-only test.
- The two collapsed edges are disjoint and go to separate points; central edge 12
  remains an edge between different vertices. Neither a collapse to one common point
  nor a localization at only the central edge has been substituted.
- Size: u and v are arbitrary, including zero, with target universe max u v;
  degreewise lifting preserves the quotient shape and does not add fibrancy.

Source: I opened https://kerodon.net/tag/05ZJ, Corollary the project server. Its quotient
collapses precisely 02 and 13 separately, and its conclusion is categorical equivalence
of the projection to the point. Its proof identifies the two localizations using
2-out-of-6. The six-step full coherent proof supplied by this DAG node is retained in
the theorem docstring. No statement correction and no STATEMENT-DISPUTED flag are needed.

Searches made for an existing statement (all msearch calls used group Q46 and this item):

- `msearch.py leanfinder`: “Collapsing opposite edges 02 and 13 of the standard three
  simplex gives a simplicial set categorically equivalent to a point”. Eight results
  (SSet.S1, six horn inclusions, SSet.Truncated.ι0₂); none gives this categorical
  equivalence. These concern circle construction or individual face inclusions.
- `msearch.py loogle`: `SSet.stdSimplex, SSet.Quasicategory`. Seven results:
  horn-filling and lifting-property characterizations of Quasicategory. None states
  the quotient's contractibility or coherent restriction equivalence.
- `msearch.py grep`: `inverse.?gadget|05ZJ|categoricalContractib`, AlgebraicTopology.
  Zero Mathlib hits.
- `msearch.py leansearch`: “The projection of the tetrahedron with edges 02 and 13
  collapsed is a categorical equivalence of simplicial sets”. Eight results on
  edges, degeneracies, endpoint projections, and the unit-vertex equivalence; none
  gives the statement. I also read Mathlib's actual `uliftFunctor`,
  `stdSimplex.isTerminalObj₀`, `stdSimplex.edge`, and `MonoidalClosed.pre` definitions.
- `rg` of the read-only upstream `WeilConjectures` and `lean/Sheaf` for
  `inverse.?[Gg]adget|05ZJ|lem-coef-inverse-gadget-categorical-contractibility`:
  no upstream match; Sheaf's SimplicialEdgeInversionPushout has Q helper definitions
  and only refers to this theorem in its proof docstring. That theorem states edge
  localization of an attachment, not categorical contractibility of Q. Importing its
  module would obstruct the eventual proof-import direction, so it is not imported.
- `rg` for `inverseTetrahedron` and `finite-inverse-tetrahedron` in the DAG and Sheaf
  found the independent, already landed construction above. I read that module and
  node and reused them. Its theorem gives extension of individual equivalence edges
  and inversion of edges under maps Q → D; it does not state a whole-functor-category
  restriction equivalence, so existing:true is not appropriate for this item.
- `rg` for the new declaration name in Mathlib, upstream WeilConjectures and Sheaf:
  no pre-existing declaration with that name.

Validation: the prescribed `scompile.py` single-file compile passed for both the sandbox
and library module checks (2.0 seconds each), with no errors or warnings. Delivery
dry run passed: `deliver2.py --no-push` printed OK and confirmed both preflight
and compilation. The worker delivers directly; the maintainer performs the independent review.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
