## Worker report

Repair of the returned immutable head 5bae368c7e3f. The retained sandbox contained
briefs but no delivered module, node record or report. This delivery supplies all
three. It follows the current shared node and its main-20261015 blueprint snapshot;
it preserves its mathematical statement, proof and proof dependencies. The
stage-1 maintenance note concerns splitting the componentwise-equivalence proof;
this stage-2 delivery preserves that proof plan and states the full conclusion.

The main module is
`Sheaf.CategoryTheory.EnrichedCategoryTensorCalculus`, with theorem
`SSet.Enhanced.Algebroid.TensorCalculus.enriched_category_tensor_calculus`.
Its 23 named declarations are recorded in `lean.declarations`. Helpers package
representatives and universal properties of this node's constructions. Structures
are data types, not choices from a postponed existence theorem. The only `sorry`
in this module is the node's final existence theorem; its docstring gives the
twelve-step natural-language proof and the prerequisite names. Every helper has
its source and this node's blueprint tag. No new independent notion/node is needed.

The theorem has a general conjunct and the integral specialization. The following
accounts for each hypothesis and conclusion of the node (unqualified names below
are in `SSet.Enhanced.Algebroid.TensorCalculus`).

1. **Two universes and smallness.** Explicit universes `u v w` are declared and
   `autoImplicit` is false. Small spaces and indexing simplicial sets use `u`;
   algebroid categories and coefficients use `max (u + 1) v`. There is no equality
   imposed between `u` and `v`. Larger-universe index shapes in limits and
   cocontinuity are restricted by the existing `Presentability.IsSmall.{u}`.
   `completeCategory.{u, v}` retains exactly the dependency's independent size
   parameters. The integral specialization uses ambient `u + 2` to accommodate
   all complexes of small modules and their enhanced localization.
2. **Presentably symmetric monoidal coefficients.** The binders are `E`,
   `hE : Quasicategory E`, `p`, `IsPresentablyMonoidal.{u, v} p`,
   `symmetry : SymmetricExtension p`, and `unit : UnitSection p`.
   `IsPresentablyMonoidal` is the existing presentability, all-small-limits and
   separate tensor-cocontinuity interface. `SymmetricExtension` is the symmetric
   cocartesian operad whose restriction is the supplied nonsymmetric monoidal
   category. Its functor Delta-op to Fin_* has the explicit interval formula on
   all pointed maps. `comparison` is an equivalence to the actual pullback,
   and cocartesian edges are preserved. Thus symmetry is the hypothesis in the
   node, not an additional conclusion presumed as input.
3. **Enriched categories and their equivalences.** All constructions use the
   dependency's `Algebroid.total`, `IsComplete`, `UnitSection` and
   `completeCategory`. `Statement.equivalences` identifies equivalence edges
   exactly with `Algebroid.IsFullyFaithful` and `IsEssentiallySurjective`.
   The existing `completeInclusion` is reused, with no duplicate definition.
4. **Presentability, limits and colimits of Cat_V.** `Statement.quasicategory`,
   `presentable` and `limits` assert these properties of that same complete
   category. Existing `Presentability.IsPresentable` includes small colimits
   and the accessible generation condition. `limits` quantifies every small
   coherent diagram, not just products or nonempty diagrams.
5. **Closed symmetric monoidal tensor.** `Statement.tensor : ClosedTensor`
   gives the binary functor and completed unit. `SymmetricTensor` supplies a
   genuine symmetric cocartesian operad, its one-colour equivalence to Cat_V,
   the active binary transport and the nullary unit. `completion_adjunction`
   is a coherent reflector adjunction. `unit_formula` identifies its unit as
   completion of the one-object unit algebroid.
6. **Objects and mapping objects before completion.** `rawTensor` is the
   existing `BinaryChangeOfEnrichment`, whose entire universal-family formula
   specifies product object spaces and postcomposition with coefficient
   multiplication on all operations. `multiplication_tensor` identifies that
   multiplication with the coefficient tensor. `multiplication_coherence`
   identifies it with the symmetric fold: concatenation, the two inert block
   projections and the fold have cocartesian comparison edges over the stated
   pointed maps. This supplies the symmetry interchange and higher compositions,
   rather than only a mapping-object assignment. `tensor_formula` says that
   the complete tensor is this raw tensor followed by completion. It does not
   assert that completion preserves the object space.
7. **Enriched internal Hom, transformations and currying.** `ClosedTensor.hom`
   is a coherent bifunctor `Cat_V.op × Cat_V → Cat_V`. `closed` gives actual
   `CoherentAdjunction` data for every partial tensor and this Hom, including
   units, counits, triangles and universal comma objects. This characterizes
   all enriched parameterized transformations. `curry` is an equivalence edge
   in Cat_V between the two internal Homs in the displayed formula;
   `curry_natural` is an equivalence of whole coherent functors on the triple
   product. The codomains remain enriched complete algebroids.
8. **Separate cocontinuity.** `ClosedTensor.colimits` is the existing
   `PreservesSmallColimitsSeparately.{u}`, in both variables and including
   empty colimits. No assertion that multiplication preserves arbitrary
   colimits of the product category is made.
9. **Limits of full inclusions and inverse-image objects.** `FullLimitProperty`
   quantifies limiting cones of small diagrams in the actual coherent arrow
   category and asserts full faithfulness of the limit arrow. `FullLimitObjects`
   also asserts the object's membership equivalence: `InImage J b` iff for
   every index `k`, `InImage (Jk k) ((Lk k).app _ b)`. The maps `J`, `Jk`, `Lk`
   are normalized by `IsUnderlyingEdge`; `targetLimitLeg` evaluates the actual
   given cone at `k` and then at the target endpoint. Hence the inverse-image
   condition refers to the original limit legs, not unrelated chosen maps.
10. **Underlying category and mapping spaces.** `Underlying.model` uses the
    existing `UnderlyingModel` with its unit-valued ordered-string simplices.
    `mapping` compares its mapping spaces with the existing `unitHomSpace`,
    namely Map_V(1,A(x,y)). `IsUnderlyingMap` specifies the image of the actual
    enriched arrow using universal-family point transport, every ordered
    simplex, and a natural comparison triangle over Delta-op. `arrows` and
    `IsUnderlyingEdge` use this normalization, including endpoint transports.
11. **Free enrichment and its adjunction.** `Diagrams.free` and `freeFunctor`
    cover all small simplicial shapes; `free_point` identifies the point with
    the completed tensor unit. `FreeScalarExtension` supplies cartesian spaces,
    the complete-Segal-nerve equivalence with Cat-infinity, and its inverse.
    `compare_normalized` uses `IsRezkClassifier`, `IsDiagramEvaluation` and
    `IsNerveEquivalenceOver` on entire diagrams, not arbitrary objectwise
    equivalences. `scalar` is strong monoidal and colimit preserving;
    `copowers` are actual colimiting cocones of the constant coefficient unit,
    with apex equal to its value at the space. Thus it is the specified
    S ↦ colim_S 1. `scalar_normalized : IsPostcomposition` fixes the induced
    map on all algebroid simplices. `free_formula` is completion after that
    scalar extension. `coherent_adjunction` gives the free/underlying adjunction
    with its actual coherent unit, counit and triangle data;
    `underlying_value` identifies its underlying values with the prescribed
    ordered-string models. `Diagrams.adjunction` also displays the expected
    equivalences on mapping spaces against the full coherent diagram core.
12. **Cotensors and arbitrary shapes.** `Diagrams.cotensor_formula` is exactly
    Hom(free K,-). `unitDiagram` and `diagram_comparison` identify its underlying
    category with the entire internal coherent functor category, including
    transformations and higher simplices. Evaluation at each `k` is normalized
    by the actual enriched evaluation. `categorification`, its natural unit,
    `categorification_quasicategory`, `categorification_universal` and
    `vertex_formula` give the freely generated infinity category for every
    small simplicial shape. The universal property is equivalence on full
    coherent functor categories. No quasicategory restriction is put on K.
13. **Hom commutes with cotensors and componentwise equivalences.**
    `commute_hom` is the displayed enriched equivalence edge;
    `commute_hom_natural` is its coherent natural version. `Evaluations.point`,
    `point_underlying`, `unitEvaluation`, `evaluation` and `evaluation_formula`
    identify evaluation as restriction along the actual enriched point and
    unit evaluation. `underlying_evaluation` is a coherent evaluation on the
    product, normalized by `evaluation_normalization`.
    `componentwise` is the iff for every transformation edge and every object
    of its source. Applying it with source `free K` and the diagram comparison
    gives the cotensor case. No H^0 criterion is substituted.
14. **Coherence.** Binary tensors are fibers of a symmetric cocartesian operad,
    internal Hom is a whole simplicial bifunctor, and its partial adjunctions
    include both triangles. Evaluation is tied by a composing 2-simplex to
    restriction of that bifunctor and unit evaluation. Currying and cotensor-Hom
    comparisons are equivalences of whole functors, retaining higher coherence.
    Operadic algebroids retain all coherent compositions and units.
15. **Opposites.** `OppositeConstruction` fixes reversal on the universal operad
    family, including its base and all ordered labels. `reverse_fibers` identifies
    coefficient reversal with transport by the actual pointed reversal
    permutation. `operation_formula` imposes the resulting formula on every
    simplex and operation, and `complete_formula` descends it by completion.
    `Statement.opposite_equivalence` and `involution` assert an involutive
    equivalence on Cat_V. `opposite_underlying` explicitly reverses each enriched
    mapping object by an equivalence in E as well as the underlying category.
16. **Enhanced unbounded D(Z).** `IntegralStatement` uses the recorded
    `IntegralDerivedCoefficients`, built from all unbounded cochain complexes
    of modules over the canonical universe lift of Z. Its localization is
    universal on entire quasi-isomorphism-inverting coherent functor categories;
    its tensor agrees on K-flat representatives with the Koszul total tensor,
    and its unit is the image of Z[0]. The conclusion supplies presentable
    monoidal coefficients and all preceding `Statement` data. Its final iff
    uses `∀ n : ℤ, IsIso (HomologicalComplex.homologyMap f n)`, detecting all
    cohomological degrees. The ordinary `DerivedCategory` is not used as an
    enhanced category.

Dependency declarations read and used (the full signatures and docstrings were
read, including those of the added already-landed statement dependencies):

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, for the original cochain/quasi-isomorphism convention.
- `Sheaf.CategoryTheory.CompleteAlgebroid`: `Algebroid.total`,
  `completeCategory`, `IsComplete`, `UnitSection`, `unitAlgebroid`,
  `monoidalSimplexBase`, `IsPresentablyMonoidal` and universal-family machinery.
- `Sheaf.CategoryTheory.AlgebroidBilinearColimits`:
  `BinaryChangeOfEnrichment`, `binaryCoefficientBase`,
  `binaryCoefficientFunctor`, `PreservesSmallColimitsSeparately`.
- `Sheaf.CategoryTheory.AlgebroidObjectSpaceFibration`: `UnderlyingModel`,
  `pointHom`, `unitHomSpace`, `IsPointTransport`, `orderedDomain`,
  `orderedMap`, `orderedLabels`, `orderedProjection`, `pointTransportDomain`.
- `Sheaf.CategoryTheory.SymmetricOperadicApproximation`: `IsOperadicTransport`.
- `Sheaf.CategoryTheory.RelativeSymmetricMonoidalLocalization`:
  `symmetricUnderlying`, `symmetricFiberInclusion`, `IsSymmetricTransport`,
  `IsSymmetricTensorOperation` (with its imported finite-pointed-set base).
- `Sheaf.CategoryTheory.AlgebroidCategoricalHomotopy`: `spatialOpPair` only;
  the downstream-looking theorem `categorical_homotopy` is not presumed.
- `Sheaf.CategoryTheory.IntegralDerivedCoefficients`: `IntegralCochains`,
  `IntegralDerivedCoefficients` (including all structure fields).
- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`: `CoherentAdjunction`;
  the independent definition node `def-coef-coherent-adjunction-data` is cited,
  rather than introducing a proof dependency on its module's Quillen theorem.
- `Sheaf.CategoryTheory.EnrichmentChangeAdjunction`: `completeInclusion`,
  `CartesianSpacesStructure`, `IsPostcomposition`, `diagramOperad`,
  `IsDiagramEvaluation`, `diagramNerve`, `diagramNerveProjection`,
  `IsRezkClassifier`, `IsNerveEquivalenceOver`.

Already-stated proof dependencies are imported: `PresentableInfinityAdjoints`,
`EnrichmentChangeAdjunction`, `SimplicialShapeCategorification`,
`SimplicialGroupoidLocalization`, `ProjectiveCochainMonoidalModel`,
`CombinatorialLocalizationPresentability`, and `AlgebroidBilinearColimits`.
The recorded proof-only nodes for algebroid presentability, completion and external
product have no Lean modules in the current shared node records; their theorem
names remain in the natural-language proof plan. No proof of those nodes is
assumed as an additional hypothesis. All eight added statement-dependency IDs
already have Lean records, and none reaches this item through statement or proof
dependencies (checked recursively against the current DAG).

Edge cases checked before and during writing:

- Empty indexing shapes are allowed in small limits, colimits and cotensors.
  The limit-of-inclusions membership condition is then vacuous, giving the
  whole terminal target. The completed tensor unit may have more than one point
  in its object-space model; only equivalence-connectedness is required, not
  contractibility of its underlying category or of its endomorphism space.
- Zero-length operadic strings are included. Pointed reversal fixes the
  basepoint and works for `n = 0`; the symmetric tensor has an explicit nullary
  unit condition.
- Non-quasicategory simplicial shapes are accepted and categorified, including
  all standard simplices and shapes with missing inner horn fillers.
- Empty enriched categories, non-discrete object spaces and arbitrary mapping
  objects are allowed. No finiteness, truncation, boundedness or nonempty-object
  hypothesis was introduced.
- The integral criterion ranges over all integers. A shifted acyclic complex
  is inverted, whereas a map inducing an isomorphism only on H^0 need not be.
- Raw pairs of objects are asserted before completion only. Hom and opposite
  formulas take place in the enriched coefficient category, not its homotopy
  category.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Presentable closed symmetric monoidal infinity
  category of complete enriched algebroids with tensor internal Hom and
  cotensors"`: eight ordinary enriched-category hits, including `EnrichedCat`,
  `EnrichedCategory` and self-enrichment of monoidal closed categories; no match.
- `msearch.py ... loogle "EnrichedCat, MonoidalClosed"`: no hits; Loogle reported
  the unqualified identifier `EnrichedCat` unknown. Source/grep searches below
  were used as well, rather than interpreting this as evidence of nonexistence.
- `msearch.py ... grep "completeCategory|enriched.*tensor"
  CategoryTheory/Enriched`: four ordinary functor-category lines, no enhanced
  algebroid statement.
- `msearch.py ... leansearch "The infinity category of complete enriched
  algebroids is presentable closed symmetric monoidal and has cotensors"`:
  eight hits in ordinary monoidal closed functor categories, enriched ordinary
  categories and AlgCat; none states this node.
- `rg` of the upstream `WeilConjectures` enriched/tensor names found ordinary
  enriched Hom and module constructions; an exact search for this node ID
  found no occurrence. Searches in `lean/Sheaf` found the dependency interfaces,
  not a declaration of this node, `SymmetricExtension` or `reversePermutation`.
  The existing `completeInclusion` found there is reused. Exact searches of
  `dag/lean_names_upstream.json` and `WeilConjectures` for
  `enriched_category_tensor_calculus`, `SymmetricExtension`, `IntegralStatement`,
  `FullLimitObjects` and `OppositeConstruction` returned no matches.
- Read the online sources [Haugseng](https://arxiv.org/html/2311.13362v1) and
  [Gepner--Haugseng](https://arxiv.org/html/1312.3178), as named in the node.
  The repaired separate-colimit argument is retained; no old inference from
  separate cocontinuity to cocontinuity on a product is used.

No statement correction or statement dispute is proposed. Every field outside
`lean` is preserved except the authorized addition of the already-landed
statement dependencies used by the interface. The dependency copy changes only
its `lean` record.

## Dependency modules

`lem-coef-enrichment-change-adjunction`: the current published source could not
compile against the selected live space nerve. `spaceSimplexObject` and
`spaceSimplexMap` forced `spaceNerveEnrichment` into explicit
`@EnrichedFunctor.obj` and `@EnrichedFunctor.map` applications, while the simplex
`r : smallSpaces _` carries the nerve's actual inferred enrichment. The compiler
reported a mismatch at `r`. The repair is exactly `(r.obj i).obj` and `r.map i j`,
letting the simplex determine that instance. Its mathematical statement,
theorem signature, complete proof docstring and every other definition are
unchanged. The dependency node changes only `lean`, with a required explanatory
note. The main module is a consumer validation: it imports this repaired module
and uses the complete-nerve classifier, postcomposition and complete inclusion.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and
the maintainer's independent review is the only review. No other agent was
started. As a self-check, I reread the node beside all structure fields and the
theorem, checked every clause in the numbered correspondence above, removed a
duplicate complete-object inclusion, added inverse-image object membership for
limits, normalized evaluation against actual enriched points, specified the
symmetric multiplication and opposite on all operadic strings, and included
the coherent free/underlying adjunction. This is not represented as an
independent reading.

## Compilation and delivery checks

Both files are compiled separately with the authorized wrapper, in dependency
order, against the live library and private side overlay:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py NC \
  lem-coef-enriched-category-tensor-calculus \
  lean/Sheaf/CategoryTheory/EnrichmentChangeAdjunction.lean \
  lean/Sheaf/CategoryTheory/EnrichedCategoryTensorCalculus.lean
```

The final run including `coherent_adjunction` and `underlying_value` returned
exit 0 with no errors or warnings: dependency overlay 12.1 s, dependency
preliminary 4.0 s, dependency sandbox 4.2 s, dependency library 8.8 s, main
sandbox 18.9 s and main library 17.2 s.

`deliver2.py NC lem-coef-enriched-category-tensor-calculus --no-push` returned
`OK (dry run): commit 3fd8c37519 passes the preflight and compiles; nothing pushed`.
It staged exactly the report, the two node records and the two Lean modules.
