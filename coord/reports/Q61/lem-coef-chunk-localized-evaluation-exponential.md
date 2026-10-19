## Worker report

The module `Sheaf.CategoryTheory.ChunkLocalizedEvaluationExponential` states
`CategoryTheory.ChunkLocalizedEvaluation.chunk_localized_evaluation_exponential`.
Its proof alone is `sorry`. All helper definitions have real data; the structures
spell out the precise construction and conclusion rather than assuming an
unconstrained comparison or an abstract exponential.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Fixed universes: `universe u w`, model objects `M : Type w`, ordinary Hom and
  simplicial mapping sets in `u`, and small indices `SCat.{u}`. `largeIndex` uses
  the dependency's `liftBundle` on `ULift` of the original object type, lifting
  each actual mapping set degreewise into `max u w`. No equality of ambient
  object and mapping universes is imposed.
- Combinatorial simplicial model category: `[Category.{u} M]`, `[ModelCategory M]`,
  `[SimplicialCategory M]`, `T : SimplicialTensorCotensor M`,
  `hC : CombinatorialModelCategory.{w,u,u} M`, and `hSM7 : SatisfiesSM7 M`.
  These are exactly the structures used by the recorded projective-model theorem.
- Small simplicial categories and enriched `v : J → I`: `SCat.{u}` and
  `EnrichedFunctor SSet (underlying J) (underlying I)` in `EvaluationSystem.spans`.
- The inline chunk notion is the already published `SimplicialChunk M`:
  its full-subcategory carrier and two enriched finite-family factorizations
  include `n = 0`. The projective diagram enrichment `E` and model `P` are the
  recorded `SimplicialDiagramEnrichment` and `ProjectiveSimplicialModelStructure`.
- Smallness of U is `ObjectProperty.Small.{u} U.carrier`; its I-chunk condition
  is `IsIChunk U T (underlying I) E P`. That definition requires both the ambient
  chunk and a chunk on exactly all U-valued diagrams, including the empty index.
- `U_f^I` and its marked weak equivalences are the existing
  `CommonChunkApproximation.diagramPair T E U.carrier`. Its objects are the full
  fibrant projective diagram subcategory with values in U; its marking is exactly
  ambient projective weak equivalence. Projective fibrations and weak equivalences
  are objectwise by the recorded projective model.
- `U^f` with its weak equivalences is `chunkPair U`, the existing `subpair` of
  `fibrantPair M`. These are full enriched subcategories with actual mapping sets.
- Enriched localization is a `LocalizationSystem B`, whose unit and
  `LocalizationPresentation` give the required derived pushout of walking arrows
  and walking groupoids. `B : BergnerModelData` supplies precisely the DK model
  from the dependency. The conclusion supplies one such functorial localization
  for the evaluation system; it does not require strict maps into arbitrary
  representatives of a derived pushout. Thus E_U(I) and X_U are respectively
  `L.functor.obj (diagramPair ...)` and `L.functor.obj (chunkPair U)`.
- P_U(I,J) is `L.functor.obj (parameterPair (diagramPair ...) (largeIndex J))`.
  `parameterPair` uses the existing coordinatewise enriched product. Its marking
  is exactly the first-component W condition together with the second component
  being an identity, allowing transport along equality of its endpoints. Hence it
  is exactly `(w,1_j)`, without saturation or marking other arrows of J.
- Actual evaluation is `Span.raw`, a marking-preserving enriched functor.
  `raw_objects` requires its object value to be F(vj), and `raw_mapping` fixes
  every degree-n simplex to `G(vu) alpha_(vj)` through the existing enriched-end
  projection and enriched composition. Enriched naturality equates the alternate
  expression `alpha_(vk) F(vu)`. `HEq` only transports the endpoint types across
  the explicit object equalities and universe lifts.
- The induced enriched evaluation is `Span.evaluation`, with
  `evaluation_induced : evaluation = L.functor.map raw`. Thus no arbitrary map
  is substituted for localization of actual enriched evaluation.
- The canonical left map is `Span.comparison`. Its first projection is precisely
  localization of `parameterFirst`; its second projection after the localization
  unit agrees in h sCat with the actual second projection. The homotopy-category
  product property makes these projection formulas characterize the comparison.
  `comparison_dk` asserts DK equivalence, and `comparison_iso` retains its inverse
  in the actual ordinary Bergner localization used for the universal property.
- The latter ordinary product represents the homotopy product:
  `Span.product_derived` uses exactly `IsDerivedLimit` and the given two projections;
  `product_limit` supplies its product universal property in the ordinary
  Bergner homotopy category. Test products are treated the same way in
  `WeakExponential.test_products`.
- Functoriality: `Restriction.objects` is enriched precomposition and
  `Restriction.mapping` pins every transformation component at every simplex.
  `chunkMap h` is the full inclusion on objects and identity on mapping sets.
  `ParameterMap` is fixed on objects and all mapping simplices by the given s.
  `ProductMap` is fixed by its two strict projection squares. For every square
  `s.comp SSet (v'.comp SSet r) = v` and full inclusion h, the field
  `EvaluationSystem.natural` asserts the evaluation square and both comparison
  projection squares in `NaturalSpanSquare`. Taking identities gives restriction
  in I, change of J, or inclusion of chunks separately. Both chunk conditions are
  explicit, exactly as in the phrase 'whenever the indicated chunks exist'.
  These actual enriched maps have their identity/composition actions fixed by
  their normalization formulas; localization preserves their functoriality.
- Exponential hypothesis: `EvaluationSystem.exponential` assumes exactly
  `bergnerCofibrant I` and selects `v = EnrichedFunctor.id`. It concludes
  `WeakExponential` for that same span, not an unrelated equivalence of Hom sets.
- For each arbitrary small test T (`K : SCat.{u}`), `uncurry` pairs a localized
  arrow with the identity using `S.product_limit`, composes with the inverse of
  the fixed localized product comparison, and then with localized evaluation.
  `WeakExponential.bijective` asserts bijectivity of precisely this function.
  `WeakExponential.natural` asserts its precomposition square for every arrow
  between test categories in the ordinary Bergner homotopy category. The test
  product cone uses the same two projections, so it denotes T ×^h I.
- Every mapping formula uses actual simplicial mapping sets and enriched ends;
  no coherent-nerve evaluation appears. The `CoherentNerve.SCat` name is the
  existing bundle for simplicial categories, not a replacement by their nerves.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `CategoryTheory.SimplicialDiagramEnrichment` (including `value` and
  `projection`), `ProjectiveSimplicialModelStructure`, and the full signature and
  proof docstring of `simplicial_projective_model_calculus`.
- `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`:
  `SimplicialLocalizationCalculus.Pair`, `PairHom`, `LocalizationSystem`,
  `LocalizationPresentation`, `fibrantPair`, `liftBundle`, `IsDerivedLimit`, and
  the recorded `simplicial_localization_comparison_calculus` signature/docstring.
- `Sheaf.CategoryTheory.SimplicialSmallChunks`: `SimplicialChunk`, both finite
  factorization structures, `IsIChunk`.
- `Sheaf.CategoryTheory.CommonChunkFilteredApproximation`:
  `CommonChunkApproximation.subpair` and `diagramPair`.
- `Sheaf.CategoryTheory.SimplicialFullyFaithfulHomotopyImage`:
  `bergnerHomotopyFunctor`, `BergnerHomotopyCategory` (ordinary DK localization).
- `Sheaf.CategoryTheory.SimplicialDiagramEquivalenceClasses`:
  `bergnerCofibrant`, defined by initial-map lifting against exactly the DK
  trivial fibrations.
- `Sheaf.AlgebraicTopology.MarkedConeExternalProduct`:
  `SSet.MarkedCone.productIndex` and its coordinatewise `productEnrichment`.
  Only these definition interfaces are reused. The external-product theorem
  node reaches this item through downstream results, so it is not added to
  mathematical stmt_deps. Reusing its existing product avoids a duplicate notion;
  that theorem is never used as a proof input.
- The stated proof dependencies' modules are imported, including
  `ExInfinityFiniteProducts`, `KanQuillenRightProper`, the diagram-class module
  and the fully-faithful image module. No recorded module is yet available for
  `lem-coef-chunk-bifibrant-localization` or
  `lem-coef-simplicial-inversion-product-parameter`; their eight-step proof uses
  remain in the theorem docstring and the node's proof plan. They introduce
  no missing object needed to type this statement. No import is fabricated.

The four already-landed owning nodes for chunk definitions, relative diagram
subcategories, the ordinary Bergner localization, and Bergner cofibrancy were
added to stmt_deps. A traversal over both dependency kinds found no path from
any of these four nodes back to this item. No natural-language statement,
proof, proof dependencies, or other node field was changed.

Edge cases checked before finishing: U empty, I empty, J empty, and the empty
finite fan/cofan. In particular U empty and I empty gives the terminal diagram
category and the empty X_U, so the asserted exponential is the terminal object
(empty raised to the empty index); no Nonempty assumption excludes this case.
J empty makes both product sources empty. Arbitrary non-Kan I and J remain
allowed for the product/evaluation part; only the exponential part assumes
Bergner cofibrancy. T need not be cofibrant. Naturality allows every derived
arrow between test categories. The object universe w remains independent of u.

Searches: the retained tool journal records leanfinder
'Localized projectively fibrant enriched diagrams in a simplicial model category
form a weak exponential in the Bergner homotopy category' (eight hits: simplicial
set monoidal closedness, enrichment and ordinary model localizations, no match);
loogle `CategoryTheory.EnrichedFunctor, CategoryTheory.exp` (no hits; exp name
unknown); and Mathlib grep `weak.exponential|chunk.*localiz|localiz.*enrich` (none).
A further LeanSearch query 'Localized enriched evaluation on small chunks
represents weak exponentials in the Dwyer Kan homotopy category' returned eight
hits: enriched ordinary-functor Hom ends and small ordinary localized Hom sets,
not the assertion. Read Mathlib's enriched-functor-category signatures: these
supply enriched ends, not enriched DK localization or the weak exponential.
`rg` on the upstream source and on `lean/Sheaf` for the above concepts and
`ChunkLocalizedEvaluation` found no existing declaration of this statement;
the upstream blueprint-id search also found none. The project's existing
product, chunk, diagram and Bergner localization definitions are reused.

Source check: opened HTT online, especially Corollary A.3.4.14 (printed p.890),
Lemma A.3.5.14 (p.896), Lemma A.3.6.17 and the evaluation spans in the proof of
Proposition A.3.6.16 (pp.904-905). The source supplies the bifibrant evaluation
bijection and the localization/product comparisons used in the node's proof.
No statement dispute or source-based correction was needed.

Validation: the full delivered module compiles cleanly through the prescribed
`scompile.py` wrapper, both under its sandbox name and its eventual library
module name. The resumed draft's unused-variable warnings were repaired.
The repaired naturality assertion covers actual commuting index squares rather
than assuming a raw evaluation square as an additional premise. The chosen
localization model is explicitly supplied with its derived-pushout presentations.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
