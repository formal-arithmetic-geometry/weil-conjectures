## Worker report

The module states `CategoryTheory.enriched_evaluation_replacement_coherence`, with
one deferred theorem proof, and gives explicit interfaces for every map in the
node. The mathematical statement, dependency lists and proof plan are unchanged.

An older module and Lean record for this item were already in the shared checkout.
I read them before deciding whether an existing declaration could serve. They do
not state the full node: evaluation and its nerve were only fixed on objects, the
interval functor and its nerve formula were absent, an arbitrary enrichment was
assumed in place of the recorded enriched end, and simplicial model axioms were
missing. The earlier component equality also compared an induced-category arrow
with an ambient arrow without applying the inclusion. This delivery replaces that
module in its owning node, rather than creating a second declaration or recording
an inexact existing match. Repository search found no consumers of the removed
helper names or applications of the theorem in other Lean modules.

Hypotheses, clause by clause:

- The ambient simplicial model category is `A`, `[Category.{u} A]`,
  `[ModelCategory A]`, `[SimplicialCategory A]`, completeness and cocompleteness,
  the two `MorphismProperty.HasFunctorialFactorization` instances, `_T`, and
  `_hSM7`. These unpack precisely the model conventions inherited from
  `lem-coef-simplicial-model-nerve-localization`; they are not hypotheses about
  a projective diagram model. No combinatoriality is assumed.
- `B I : CoherentNerve.SCat.{u}` supply the small simplicial categories and
  `_hB : IsLocallyKan B` is the local Kan condition. No such condition is placed
  on `I`. All objects and mapping sets live in one sufficiently enlarged universe,
  as expressly allowed by the node. `autoImplicit` is false and `u` is explicit.
- `E : SimplicialDiagramEnrichment (underlying I) A` is the dependency's actual
  enriched-end presentation. `E.Diagrams` is its existing category, not an arbitrary
  extra enrichment and not a projective model category.
- `H : Fin 2 → EnrichedFunctor SSet B E.Diagrams` is exactly the pair `H₀,H₁`.
- `q : GradedNatTrans (𝟙_ (Center SSet)) (H 0) (H 1)` uses Mathlib's existing
  genuinely enriched naturality definition. Its `naturality` is an equality of
  simplicial maps on the whole mapping object. `diagramComponent E q b` merely
  converts its unit-shaped component to a vertex arrow via `eHomEquiv`.
  Naturality inside `I` comes from `E.represents` and `represents_projection`.
- `_h` says every value of each of the two families is both `IsCofibrant` and
  `IsFibrant`, without assuming diagram cofibrancy or diagram fibrancy.
- `_hq` says every `SimplicialDiagramEnrichment.component` of those vertices is a
  `WeakEquivalence` in the given model structure on `A`.
- `K : SSet.{u}` and `a : K ⟶ CoherentNerve.nerveFunctor.obj I` are arbitrary;
  no equivalence, nonemptiness, or quasicategory assumption is made on `K` or `a`.

Conclusions, clause by clause, are fields of `CoherentEvaluation.Comparison`:

- `evaluation` gives the two enriched functors into the actual `Bif A`.
  `evaluation_objects` is exactly `e_j(b,i)=H_j(b)(i)`.
  `evaluation_mapping` fixes the complete simplicial map by end projection,
  the action of `H_j(c)` on `I(i,k)`, and enriched composition. Thus this is the
  specified evaluation, not an existential functor with only the same objects.
- `transformation`, `transformation_components`, and `transformation_naturality`
  give the enriched evaluated transformation with exactly the component `q_b(i)`.
  `.hom` applies the ordinary bifibrant-subcategory inclusion before comparison
  with the arrow in `A`. `HEq` transports only the displayed endpoint equalities.
- `intervalFunctor` is the required enriched functor on `(B×I)×[1]`.
  The existing Mathlib thickening of the two-element order is used for `[1]`:
  its nonempty mapping posets are singletons, so its enrichment is discrete.
  `interval_objects`, `interval_same_level`, and `interval_cross` specify its
  entire mapping-simplex formula at levels 00, 11, and 01 respectively. Level
  10 is empty and has a unique map. The cross formula is `r_y e₀(f)`; enriched
  naturality identifies it with `e₁(f) r_x`.
- `productComparison` and `intervalProductComparison` record the canonical nerve
  product isomorphisms. `NerveProduct.objects` and `mapping` fix them in every
  simplicial degree, including all enriched mapping objects. `intervalNerve`
  identifies the interval nerve with Delta[1], with every object of every simplex
  fixed by `interval_nerve_objects`. Since the target interval is a poset with
  singleton nonempty mapping objects, that fixes the complete nerve map.
- `coherentEvaluation` gives `E_j`; `coherent_evaluation_formula` identifies it
  with the precise nerve of `evaluation j`, precomposed by identity times `a`,
  and curried, with the explicit symmetry needed for Mathlib's left internal hom.
- `edge` is a genuine edge in `Fun(N_hc B, Fun(K,N_hc(A^cf)))`.
  `edge_source` and `edge_target` identify its endpoints as exactly the two `E_j`.
  `edge_formula` fixes it as the twice-curried nerve of `intervalFunctor`, with
  both canonical product comparisons, the restriction `a`, and the necessary
  associator and symmetry written explicitly. This retains all higher coherence.
- `edge_equivalence` is the dependency's two-inverse-triangle definition of an
  equivalence edge in that outer functor simplicial set.
- `edge_components` evaluates this very edge at both vertices and identifies its
  arrow, after the bifibrant inclusion, with exactly `q_b(a(k))`. The vertex of
  `I` is read from the zero-simplex enriched functor at its unique object.
- No assertion or assumption that either `E_j` is an equivalence is introduced.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.SimplicialModelLocalization.Bif`, `SatisfiesSM7` and the
  signature and proof plan of `simplicial_model_nerve_localization`.
- `Sheaf.CategoryTheory.CoherentNerveComparison` and its public infrastructure:
  `CoherentNerve.SCat`, `underlying`, `IsLocallyKan`, `nerveFunctor`, and
  `coherent_nerve_comparison`, including its discrete and locally Kan clauses.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge`, `evaluation`, `diagramVertex` and the
  existing internal hom used for coherent functor categories.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `SimplicialDiagramEnrichment`, its `Diagrams`, `value`, `component`,
  `projection`, `represents`, `represents_projection` and composition equations.
  I also checked this module through `scompile.py --source` against the current
  published source. Its model-structure existence theorem is not a hypothesis.
- `Sheaf.AlgebraicTopology.MarkedConeExternalProduct`:
  `SSet.MarkedCone.productIndex` and `productEnrichment`; I read their full
  definitions and the owning theorem's signature and docstring.
- Proof-only imports: `Sheaf.CategoryTheory.PointwiseEquivalences`, declaration
  `SSet.Enhanced.pointwise_equivalences`, and Mathlib's inner-anodyne
  pushout-product module, declaration `innerAnodyneExtensions_pushoutObjObjι'`.
  `lem-coef-joyal-strict-currying` has no recorded Lean module, so no nonexistent
  proof import is added; the statement uses Mathlib `MonoidalClosed.curry`.

Edge cases checked before and after writing: empty `B`, empty `I`, empty `K`,
`K=Delta[0]`, identity `q`, a one-object index, constant `a`, and non-locally-Kan
`I`. The empty cases make only the relevant component conditions vacuous; the
canonical product/interval maps and the equivalence in the terminal functor object
remain present. No diagram cofibrancy, essential-surjectivity condition, or
finite-dimensional restriction enters. For the interval, I checked all possible
composable level triples 000, 001, 011, 111 and the empty backwards mapping object.

Searches made:

- `msearch.py leansearch`: "Enriched natural weak equivalences induce coherent
  natural equivalences after simplicial evaluation and nerve" returned eight hits,
  notably `SimplicialNerve`, `Enriched.FunctorCategory.homEquiv`,
  `EnrichedFunctor.hom_ext_iff`, and `EnrichedNatTrans.mk`. None states this node.
- `msearch.py leanfinder`: "Enriched evaluation and objectwise weak equivalences
  induce coherent natural equivalences of simplicial diagrams" returned eight
  hits, including `Enriched.FunctorCategory.homEquiv`, transported enrichments,
  `SimplicialObject.instEnrichedCategorySSet`, and `SimplicialCategory.homEquiv'`.
  These supply building blocks, not the interval comparison.
- `msearch.py loogle`: `"EnrichedNatTrans", "SimplicialNerve"` returned no hits.
- `msearch.py grep` in `CategoryTheory`:
  `enriched.*evaluation|replacement.*coherence|intervalFunctor` returned no hits.
- Direct `rg` in upstream `WeilConjectures` for
  `enriched.*evaluation|evaluation.*replacement|coherent.*evaluation`, for the
  item id, and for `SimplicialDiagramEnrichment` returned no existing statement.
- Direct `rg` in `lean/Sheaf/CategoryTheory` for evaluation/replacement and
  `SimplicialDiagramEnrichment` found the older module of this same item and
  related localized evaluation modules. I read the old module in full and checked
  its missing clauses, rather than rebinding it as an exact match.
- Read Mathlib `Enriched/Basic.lean` on `GradedNatTrans`, `EnrichedNatTrans`,
  `ForgetEnrichment`, and enriched functor composition; read
  `Enriched/Ordinary/Basic.lean` on `eHomEquiv` and whiskering. In particular,
  `EnrichedNatTrans` alone only records underlying ordinary naturality, so the
  new statement uses the existing `GradedNatTrans` instead.
- Read Mathlib `SimplicialNerve.lean` on the full thickening and nerve formulas,
  `StdSimplex.lean` on simplex evaluation and `yonedaEquiv`, and
  `Monoidal/Closed/FunctorToTypes.lean` on the internal hom and transpose.

Sources checked directly: [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Definition 1.1.5.5 and Example 1.1.5.8 (printed page 22), and
[Kerodon 01DK](https://kerodon.net/tag/01DK). The elementary interval construction
is the agent-written argument already recorded in the node, not a new claim that
these references state its entire two-parameter formula.

No new DAG nodes, dependency replacements, statement correction or
STATEMENT-DISPUTED flag is required. All auxiliary declarations belong to the
owning node's canonical construction and are listed in `lean.declarations`.
Definitions contain real data; no data is chosen from the theorem's existence
claim. The single theorem has exactly `by sorry`, with the six-step proof in its
docstring.

## Author check

I reread the node and the final module together. This found and repaired the old
vertex-only comparison, missing interval construction, incorrect arrow encoding,
and insufficient enriched transformation interface. I checked tensor composition
parentheses, the direction of the associator for twice currying, the ordering of
the two variables, and face 1 as source / face 0 as target. I am the author;
the independent review is the maintainer's review, as specified in this brief.

## Second reading by NE

Independent maintainer reading of immutable delivery
`c1b1616cde256670ee5f02a836cf8b16c567a42f`, performed on 2026-10-17.
This reader did not author or second-read the delivery. The original worker text
is retained above; this section replaces its non-substantive placeholder.

### Hypotheses and conclusions

1. The ambient `A`, its category, model structure and simplicial enrichment are
   precisely the node's simplicial model category. `HasLimits`, `HasColimits`,
   both functorial factorization instances, `SimplicialTensorCotensor` and
   `SatisfiesSM7` unpack the conventions explicitly stated in the dependency
   `lem-coef-simplicial-model-nerve-localization`. They do not add combinatoriality
   or a diagram model structure. SM7 uses the actual pre/postcomposition corner
   map, Kan fibrations and weak equivalences, rather than an arbitrary predicate.
2. `B I : SCat.{u}` are the specified small simplicial categories. Only `B`
   has the `IsLocallyKan` hypothesis. The single explicit universe is consistent
   with the node's express permission to enlarge universes to contain both
   indices and the ambient category. No coefficient or site universe is silently
   identified here. `autoImplicit false` excludes unbound automatic variables.
3. `E` is the dependency's enriched-end presentation, not arbitrary ordinary
   enrichment: `represents` identifies its mapping objects with
   `enrichedNatTransYoneda`, `represents_projection` fixes evaluations, and
   `projection_id`/`projection_comp` fix composition. This is usable without
   the dependency's combinatorial projective-model existence theorem.
4. `H : Fin 2 → EnrichedFunctor ...` is the ordered pair of families.
   `GradedNatTrans (𝟙_ (Center SSet))` gives component vertices and naturality
   on entire mapping objects. In Mathlib, `EnrichedNatTrans` alone has only
   underlying ordinary naturality, so using `GradedNatTrans` here is necessary.
   `diagramComponent` converts the unit-to-hom map via `eHomEquiv`; the existing
   end projection supplies its component at `i`.
5. `_h` requires bifibrancy at every `(j,b,i)`, with neither projective
   cofibrancy nor projective fibrancy. `_hq` is weak equivalence of exactly
   `q_b(i)` in `A`. `K` and `a` are arbitrary; neither is required to be
   nonempty, locally Kan, a quasicategory, or an equivalence.
6. `Comparison.evaluation` has target the actual full subcategory `Bif A`.
   `evaluation_objects` fixes values; `evaluation_mapping` is end projection
   of `H_j(u)` followed by the action of `H_j(c)` and `eComp`, namely
   `H_j(c)(v) ∘ H_j(u)_i` in all simplicial degrees. End naturality gives
   the other order in the node. `transformation_components` fixes `q_b(i)`
   after the full-subcategory inclusion `.hom`; `transformation_naturality`
   is equality of simplicial maps, not just vertex naturality.
7. The interval is Mathlib's thickening of the two-element linear order.
   Its 00, 01 and 11 mapping posets each have one element, and its 10 mapping
   poset is empty. Thus it is the discrete enriched `[1]`. `interval_objects`,
   `interval_same_level` and `interval_cross` fix the interval functor on all
   objects and mapping simplices. The cross formula is `r_y e_0(f)`;
   naturality gives `e_1(f) r_x`. The backwards map is unique. The possible
   composable levels 000, 001, 011 and 111 all satisfy the stated formula.
8. `NerveProduct.objects` and `mapping` fix the product comparison degreewise
   as pairing enriched functors, not merely as an arbitrary nerve isomorphism.
   `interval_nerve_objects` fixes the interval nerve map in every degree; the
   interval's singleton/empty mapping objects determine the remaining maps.
   These data therefore determine the canonical maps up to the equalities used.
9. `coherent_evaluation_formula` is precisely restriction by `1 × a` and
   currying of the nerve of evaluation. For `X = N_hc B`, Mathlib curry
   transposes `K × Y → Q` to `Y → Fun(K,Q)`. In `edge_formula`, the inverse
   associator sends `K × (X × Δ[1])` to `(K × X) × Δ[1]`, then the symmetry
   gives `(X × K) × Δ[1]`. Applying `1 × a`, the product comparisons and
   the nerve of the interval functor, then currying twice, gives exactly
   `Δ[1] → Fun(X,Fun(K,Q))`. The factor order is correct.
10. `edge_source` uses face 1 and `edge_target` face 0, correctly identifying
    the prescribed endpoints. `edge_equivalence` uses the dependency's actual
    two inverse-triangle definition. `componentEdge` evaluates the same edge
    twice; `edgeArrow` reads the unique distinguished interval path.
    `edge_components` compares its included arrow with exactly `q_b(a(k))`.
    The heterogeneous equalities transport the displayed object equalities;
    they do not compare incompatible full-subcategory and ambient arrow types.
    There is no assertion that either endpoint functor is an equivalence.

### Sources and dependency inspection

Read the item node, all six proof steps and all five statement-dependency nodes
in the immutable snapshot, and the exact relevant definitions and docstrings in
the read-only NE clone. The dependency declarations inspected were:

- `SimplicialModelNerveLocalization.lean`: `cornerMap`, `SatisfiesSM7`, `Bif`,
  `IsOrdinaryNerveMap` and `simplicial_model_nerve_localization`, including the
  normalization of the bifibrant comparison by inclusion followed by localization.
- `CoherentNerveComparison.lean`: `CoherentNerveComparisonStatement` and
  `coherent_nerve_comparison`; `CoherentNerveInfrastructure.lean`: `SCat`,
  `underlying`, `hom`, `IsLocallyKan` and `nerveFunctor`.
- `EnhancedDiagramsCones.lean`: `IsEquivalenceEdge`, `diagramVertex` and
  `evaluation`, which use the existing internal hom.
- `SimplicialProjectiveModelCalculus.lean`: `SimplicialDiagramEnrichment`,
  its representation/projection laws, `Diagrams`, `value` and `component`.
- `MarkedConeExternalProduct.lean`: `productEnrichment` and `productIndex`.
  Only its real coordinatewise product construction is used; no marked-model
  theorem is needed to state this item.
- Proof support: `PointwiseEquivalences.lean`, `pointwise_equivalences`,
  and Mathlib's inner-anodyne pushout-product statement. The proof-only
  currying dependency has no recorded module; the statement uses the existing
  Mathlib `MonoidalClosed.curry` directly and adds no nonexistent import.

Read online [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Definitions 1.1.5.1 and 1.1.5.5, Example 1.1.5.8 (printed pp. 20–22),
Proposition 1.2.7.3 (p. 39), and Proposition 4.2.4.4 (p. 258), and
[Kerodon Theorem 4.4.4.4](https://kerodon.net/tag/01DK).
The node labels its two-parameter construction as an agent argument; these
sources support its nerve and pointwise-equivalence ingredients, rather than
asserting the whole formula as a verbatim published theorem. In particular,
the combinatorial hypothesis of HTT 4.2.4.4 is not needed for this elementary
transformation construction and is correctly absent from the Lean statement.

The six-step proof docstring matches the DAG: enriched-end evaluation,
two-variable enriched naturality, interval extension, actual nerve/currying,
inversion of bifibrant weak equivalences, and two applications of the pointwise
criterion. The inner-horn pushout-product argument supplies the required
quasicategory target before the second application. No missing helper,
§1(B) repair, or §1(C) statement correction is needed.

### Searches, edge cases and pilot gates

Independent `rg` searches in Mathlib, upstream `WeilConjectures`, and the NE
`lean/Sheaf` tree used `GradedNatTrans`, `SimplicialNerve`, `intervalFunctor`,
`nerveProduct`, enriched evaluation and evaluation/replacement variants.
The old module at this same owning node has only vertex-level comparisons,
no specified interval nerve, and an inexact transformation interface. It is not
an exact existing match. Related rectification/evaluation theorems have different
conclusions. Mathlib's `Enriched/Basic.lean:442–500`,
`AlgebraicTopology/SimplicialNerve.lean:50–210` and
`Monoidal/Closed/Basic.lean:146` provide the building blocks, not this theorem.
LeanSearch query "simplicial enriched natural transformation weak equivalence
coherent nerve functor category" returned eight hits, led by `SimplicialNerve`.
LeanFinder query "The homotopy coherent nerve carries enriched natural weak
equivalences between bifibrant valued families to natural equivalences" returned
eight ordinary/truncated-nerve hits. Neither is an exact match. The original
worker's three search kinds remain recorded above.

Checked empty `B`, empty `I`, empty `K`, `K = Δ[0]`, one-object indices,
identity `q`, constant `a`, and non-locally-Kan `I`. Empty component conditions
are vacuous but do not delete the canonical comparison or equivalence conclusion.
No `Nonempty` binder excludes them. Dimensions zero and one, both interval
endpoints, and the empty backwards mapping object are covered. There is no
characteristic, coefficient ring, scheme, or pro-etale substitute in this item.

All seven declarations have source-place and blueprint docstrings. Definitions
contain real data or fully pinned comparison structures, with no choice from
unconstrained existence and no `sorry` in data. The only deferred proof is the
named theorem's `by sorry`. No additional local theorem is proved. Names have
no `Sheaf.` prefix, imports obey the statement/proof convention, lines are at
most 100 characters, and the node's `lean.statement` equals the theorem signature
verbatim in both original and fixed modules. All seven explicit declaration
names are recorded. The mathematical node statement is unchanged, so no citer
audit for a statement correction is required. No consumers of the removed old
helper names were found outside the old owning module.

### Compiler evidence and findings

The delivered report did not contain a per-file compiler transcript; the item's
record asserted repeated clean compiles. Reproduced independently with:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py NE \
  lem-coef-enriched-evaluation-replacement-coherence \
  snapshot/lean/Sheaf/CategoryTheory/EnrichedEvaluationReplacementCoherence.lean
```

Exit 0: sandbox `Sheaf/Stage2/Sandbox0.lean` 3.5 s; library
`Sheaf/CategoryTheory/EnrichedEvaluationReplacementCoherence.lean` 3.7 s;
no errors or warnings. The installed wrapper is dated 2026-10-17 and uses
server `nt_srv_compile.py --wire-confirm`; unlike the older brief's description,
it currently routes the private side overlay checks through the server.
Only that authorized wrapper was invoked, with its unchanged 60-second limit.

Findings repaired in the complete files under `fixes/`:

- H11 (and the substantive report requirement in H1): the original
  `## Second reading by NE` was only a disclaimer. Replaced it with this actual
  independent clause-by-clause reading, explicitly attributed to the maintainer.
- H8 / brief §3 documentation convention: added the missing main definitions
  and main statements list to the module docstring. No declaration changed.
- Corrected the worker report's corrupted "Definition the project server and
  Example the project server" citation to Definition 1.1.5.5 and Example 1.1.5.8.

Recompiled the complete fixed module through the same wrapper: exit 0,
sandbox 2.6 s and library 3.6 s, no errors or warnings. The theorem signature
remains byte-for-byte equal to `lean.statement`; the module after its docstring
is byte-for-byte unchanged. No mathematical defect was found.

No global build, direct SSH command, repository edit, claim, delivery, merge,
or Git mutation was performed. The immutable snapshot and branch were not
changed. The review directory is an extraction, not a Git checkout; no branch
head was reset or moved. Landing/preflight tools were read for fix-file format
only and were not run. The fixes use the exact module path and
`<item>.report.md` names accepted by `merge_delivery.py --stage 2 --apply-fixes`.
