## Worker report

N5, 2026-10-17. Stage 2 only. The main module is
`Sheaf.CategoryTheory.DayRelativeExponentialModel`; the main declaration is
`SSet.Enhanced.DayModel.day_relative_exponential_model : Nonempty Statement.{u, v}`.
The theorem is `sorry`. Its docstring contains the node's twelve proof steps, including
all named prerequisite references. The helper definitions have real construction data;
none extracts an undetermined object from a postponed existence theorem. All 50 owning
module declarations are recorded in `lean.declarations`.

The mathematical statement is unchanged. Four already-landed statement dependencies
were added to name existing helper interfaces used in the signature:
`lem-coef-presheaf-external-product-kan`,
`lem-coef-cat-infinity-opposite-involution`,
`lem-coef-infinity-isofibration-pullback-limit`, and
`def-coef-coherent-adjunction-data`. No new definition node or private copy of those
notions was introduced. There is also one prerequisite compilation repair, described
below. No STATEMENT-DISPUTED issue was found.

### Hypotheses and clauses

All names in the following list without a namespace prefix belong to
`SSet.Enhanced.DayModel`.

1. **Quasicategories, coherent functors, sizes.** `CatInfinity.{u}` and the existing
   internal hom `ihom` are used throughout. `Statement.base_quasicategory` and
   `Statement.quasicategory` assert the required instances. The small total categories
   are in `SSet.{u}`, presheaves and RFib in `SSet.{u+1}`; arbitrary parameter categories
   are in `SSet.{max (u+1) v}`. `ambientRightFibrations`, `ambientProjection`,
   `transportSpaces`, and `Enlargement` make these inclusions explicit. The parameter
   universe `v` is independent of `u`; there is no extra universe equality. The
   `Enlargement` object and arrow equations normalize the enlargement to actual ULift,
   and its full faithfulness rules out a change of the small categories involved.

2. **RFib and target evaluation.** `arrows` is exactly `Fun(Δ[1], CatInfinity)`;
   `arrow` decodes its vertex to the actual functor. `rightFibrations` is the existing
   `fullSubcomplex` on `rightFibration (catInfinityArrow ...)`. Thus squares and every
   higher coherent simplex of the full subcategory are retained. `projection` is its
   inclusion followed by evaluation at vertex 1; it is not a chosen classifier map.

3. **Both fibrations, fibers, restriction and Kan extension.**
   `Statement.cartesian` and `.cocartesian` concern this actual `projection`.
   `presheaves D` is the full functor object from the lifted `oppositeSSet D` to the
   existing `smallSpaces`; `restriction h` is literal precomposition by `h^op`.
   `FiberCalculus.comparison` and `.equivalence` identify each actual fiber with this
   presheaf category. `.transport` requires entire cartesian and cocartesian transport
   functors and cylinders, not just maps on objects. The cartesian comparison is with
   `restriction`; the cocartesian comparison is with a coherent left adjoint to that
   exact restriction. `CoherentAdjunction` includes its coherent unit, counit, triangles
   and universal comma conditions, which characterize left Kan extension. The
   `IsTransport` cylinders fix endpoints and the underlying base arrow.
   `Statement.cartesian_squares` compares cartesian edges with the cartesian edges of
   actual ambient target evaluation. The arrow-source-fibers prerequisite identifies
   these with pullback squares (by its opposite dual); no arbitrary square predicate is
   substituted.

4. **Finite products, terminal arrow and external products.**
   `ProductCalculus.products` is the existing finite-product universal-property
   predicate. `.arrow_products` says the RFib inclusion preserves those products, so
   they are actual arrow products. `.preserves` says target evaluation preserves them.
   These predicates include the empty index, hence include the terminal arrow `*→*`.
   `.external` quantifies over every finite `I : Type u` including the empty type.
   It forms the actual degreewise product arrow with `ExternalKan.tuple` and
   `ExternalKan.projection`, asserts it is right fibrant, and identifies its classifier
   with `externalProduct`. The latter uses the existing `ExternalKan.multiply` on
   whole coherent diagrams, precomposed with the opposite projections. `IsClassified`
   uses the normalized existing space-transport classifier and an equivalence over
   the actual base, including the inverse homotopies over that base.

5. **All relative sections and intrinsic fiber.** `sections D` is the existing full
   `relativeOperadicDiagrams D ambientProjection`; it has no marking or
   edge-preservation condition. `HasIntrinsicSectionFibers` tests its strict fiber
   square by `pullbackCoreComparison` against every test quasicategory `Q`, asking for
   the canonical constant-path comparison to the homotopy pullback to be a weak
   equivalence. This expresses the infinity-categorical fiber, retaining the coherent
   identification with `D`, rather than replacing it by an unqualified set of objects.
   `Statement.intrinsic_fibers` asserts that condition.

6. **The specified opposite unstraightening and section equivalence.**
   `UniversalData.diagram` is the full coherent opposite involution followed by the
   normalized universe enlargement. `universalObject` actually applies the recorded
   `CocartesianStraightening.Statement.equivalences.unstraighten` to that diagram;
   `UniversalData.total` and `.projection` are its actual total space and map. For
   arbitrary `K,D`, `SectionComparison.map` has target
   `Fun(pullback D (ulift U.projection), transportSpaces)`. This is the base change of
   that unstraightening, hence the `X_D` specified by the node. Its `.equivalence`
   concerns full functor categories. `UniversalClassifier.sections` requires this for
   every `K` and `D` in the arbitrary containing universe.

7. **Value, transformations and naturality of section classification.**
   `UniversalClassifier.map` is over `projection`; `.classifies_fibers` identifies the
   decoded actual right-fibration arrow with its presheaf under `FiberCalculus`.
   `.opposite_fibers`, `.opposite_equivalences`, and `.fiber_formula` identify its
   evaluation with that presheaf on every transformation simplex and every simplex of
   the opposite fiber. `SectionComparison.formula` fixes the value of the comparison
   on every `n,k,s,a,z`, using that same universal evaluator. Thus the equivalence
   retains whole mapping spaces and all higher simplices. Both base restriction and
   pullback along coherent transformations use this single evaluator and its actual
   opposite unstraightening, so their comparisons have the same evaluation formulas;
   no independent objectwise choices or preservation restrictions are introduced.

8. **The exact ordered-block base.** `OrderedBlocks.functor` is an ordinary functor
   `SimplexCategoryᵒᵖ ⥤ FinStar`. `.objects` fixes the arity to the simplex length.
   `.values` specifies, for every input and output coordinate, the biconditional
   `a(j-1) < i ≤ a(j)` with the output indexing translated from 1-based coordinates
   to `Fin`. A pointed map has no other non-basepoint values, so all other inputs go
   to the basepoint. Empty intervals are permitted. `orderedBase` is the actual nerve
   of this functor, with only the necessary up/down size transport.

9. **Actual envelopes, their map, fibers and block Kan transport.**
   `EnvelopeCalculus.map` is normalized, after the existing envelope inclusion, to
   `postcompose indexProjection projection`. This fixes every simplex of the induced
   envelope map. Its `.over` equation fixes the finite-pointed-set base.
   `orderedEnvelopeMap` is the actual pullback map along `orderedBase`.
   `Statement.ordered_cocartesian` asserts that map is a cocartesian fibration.
   The existing `CartesianEnvelope.total` is the full product-diagram envelope, with
   tuple fibers and normalized singleton comparisons. Its tuple fiber over `(D_i)`
   is the product of the original fibers; `FiberCalculus.equivalence` therefore
   identifies it with `∏ P(D_i)`. `Statement.ordered_block_transport` is an iff with
   `BlockCocartesian` on the actual envelope edge: every retained output block is
   `projection`-cocartesian at the crossing component of that product diagram.
   Its source is the block's product right fibration, classified by the external
   product by clause 4; its target is therefore the left Kan extension along the
   actual block functor by clause 3. Empty blocks use the empty product cone and its
   terminal presheaf. This specifies the stated transport, including discarded inputs.
   No symmetric-envelope claim stronger than the stated ordered pullback is required.

10. **Classifying algebra of the given monoidal category.** `Statement.monoidal`
    quantifies over every small quasicategory `V` and every
    `p : V → monoidalSimplexBase` satisfying the existing
    `IsMonoidalInfinityCategory`. `ClassifyingAlgebra` compares this very `p`, over
    the base and by a full functor equivalence, with an actual cocartesian
    unstraightening object. Its full straightening diagram agrees with
    `baseLift.hom ≫ algebra ≫ baseProduct`. Its `.singletons` are exactly
    `monoidalUnderlying p`. Combined with the full product-diagram envelope and its
    inert algebra condition, this identifies the classifying algebra on tuples,
    tensors, units and their coherences, rather than choosing unrelated block maps.

11. **Day pullback, presheaf powers, operations and inert criterion.**
    `dayTotal P algebra` is literally `pullback algebra P.map`, with its actual
    projection `dayProjection`. `DayPullback.over` and `.inert_algebra` place it over
    the specified ordered base. `.monoidal` asserts both its quasicategory and the
    existing monoidal-cocartesian-fibration predicate. `.fibers` and the normalized
    `MonoidalData.comparison`/`.equivalences` give `P(C)^r` for every natural `r`.
    `.comparison_inert` identifies all coordinate projections with inert transport;
    `.singleton_formula` fixes the singleton RFib map in every simplicial degree,
    and `.comparison_one` fixes its comparison to the existing presheaf classifier.
    The block criterion of clause 9, specialized to the tensor blocks of clause 10,
    is exactly left Kan extension of external products along opposite tensor, hence
    the stated Day operation. All quantifiers include `r=0` and empty blocks.
    `DayPullback.inert` is precisely the asserted iff between cocartesian edges over
    inert base arrows and inert envelope images.

12. **Universal product section and coherent evaluation.**
    `IsTotalProduct` reads the full-subset value of every envelope simplex.
    `EnvelopeCalculus.totalProduct_formula` and `.baseProduct_formula` fix the actual
    total products. `.product_square` places `productSection` over `productDiagram`.
    `productSection` is thus the actual universal product right fibration over Day;
    clause 6 applies with parameter `K=dayTotal`, using `v` large enough and leaving
    the small space values unchanged. `evaluationDomain` is exactly the common-base
    pullback of Day and the opposite product-category unstraightening, namely
    `Q_C ×_S C^{op,⊗}`. `DayEvaluation.formula` evaluates `productSection ≫ E.map`
    on every simplex. Clauses 4 and 7 identify the value with `∏ F_i(c_i)` and fix
    its higher simplices. Literal base restriction preserves this formula.

13. **Strong monoidal naturality and lax restriction.** `Statement.restriction`
    quantifies over the given monoidal categories and every base-preserving strong
    monoidal `f` (existing `IsStrongMonoidalInfinityFunctor`).
    `RestrictionData.originalArrow`/`.original_formula` identify the actual coCart
    edge of `f`; `.classifying_square` identifies its straightening with the
    specified coherent `baseTransformation`, with equivalence sides.
    `.opposite_transport` is cocartesian transport of the actual universal opposite
    unstraightening along that transformation. Thus `.oppositeMap` is induced by
    the given `f`, not an arbitrary map with the right endpoint types.
    `.right`, `.right_over`, and `.fibers` specify coordinatewise presheaf restriction;
    `.right_lax` preserves inert edges. The left functor preserves all cocartesian
    edges, and `.adjunction`/`.relative` give the coherent relative adjunction, with
    unit and counit over identity base arrows. Its mates therefore specify the lax
    tensor and unit maps. On the canonical common domain `Q_C' ×_S C^{op,⊗}`,
    `.source_first`/`.source_second` and `.target_first`/`.target_second` fix the two
    comparison maps by the pullback projections. `.evaluation` is a natural
    equivalence of the entire resulting evaluation functors, including higher
    simplices. Arity-zero comparison and identity `f` remain included.

14. **No essential-image substitute.** There is no essential-image predicate or
    vertexwise subset standing in for the displayed section equivalence. The
    relative exponential is only the existing full coherent evaluator representing
    functors on opposite unstraightening. Day itself is the actual envelope pullback.

### Dependency declarations and imports

The five original statement dependency modules were opened at their recorded signatures:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex`,
  `mappingSpace`, `AreNaturallyEquivalent`, `IsFunctorEquivalence`, and the full
  coherent diagram/relative-diagram conventions.
- `Sheaf.CategoryTheory.SpaceTransportClassification`:
  `SSet.Enhanced.smallSpaces`, `transportSpaces`, `TransportClassifier`,
  `TransportClassificationClauses`, `TransportOverEquivalence`, and
  `space_transport_classification`. Right/cartesian/cocartesian fibration predicates
  are the existing interfaces imported by that module.
- `Sheaf.CategoryTheory.CocartesianStraightening`:
  `SSet.Enhanced.CocartesianStraightening.Statement`, `.Objects`, `.coCart`, `.object`,
  `.diagrams`, `.classify`, and `cocartesian_straightening`.
- `Sheaf.CategoryTheory.CartesianOperadicEnvelope`:
  `SSet.Enhanced.CartesianEnvelope.total`, `.complex`, `.projection`, `.Index`,
  `.IndexHom`, `.indexProjection`, `.indexVertex`, `.indexArrow`, `.productObject`,
  `.HasFiniteProducts`, `.PreservesFiniteProducts`, and `cartesian_operadic_envelope`.
- `Sheaf.CategoryTheory.MonoidalInfinityCategory`:
  `SSet.Enhanced.monoidalSimplexBase`, `monoidalBaseVertex`, `monoidalRho`,
  `monoidalUnderlying`, `IsMonoidalInfinityCategory`, `IsMonoidalTransport`,
  `IsMonoidalInertEdge`, and `IsStrongMonoidalInfinityFunctor`.

The four added existing statement interfaces are public imports:

- `Sheaf.CategoryTheory.PresheafExternalProductKan`:
  `SSet.Enhanced.ExternalKan.product`, `.projection`, `.tuple`, `.multiply`.
- `Sheaf.CategoryTheory.CatInfinityOppositeInvolution`:
  `SSet.Enhanced.catInfinityObject`, `catInfinityArrow`, `catInfinityThickEdge`,
  `IsCatInfinityOpposite`.
- `Sheaf.CategoryTheory.IsofibrationPullbackLimit`:
  `SSet.Enhanced.pullbackCoreComparison` (the canonical constant-path map).
- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction`, bound by the existing
  definition node `def-coef-coherent-adjunction-data`.

The available proof-dependency modules are imported for stage 3:
`CatInfinityFilteredFiniteCalculus`, `ArrowSourceFibers`,
`PointwiseCocartesianTransport`, `InfinitySpaceValuedPointwiseLan`, and
`InfinityYonedaPresheafLimits`. Other recorded proof dependencies whose modules were
already statement imports are public imports. The remaining proof-dependency nodes had
no usable recorded module at inspection time; their names and proof uses remain in the
main theorem's docstring. No purported proof of those prerequisites is introduced.

### Edge cases and searches

Checked by reading the complete quantified signatures and construction data: empty
and terminal `D`; empty, point and arrow parameter `K`; finite index empty or singleton;
arity zero and one; empty retained intervals, discarded coordinates and no outputs;
identity base arrows and identity strong monoidal functors. No nonempty, filteredness,
positive-arity, or preservation hypothesis was added. Transport is defined with the
correct cartesian reversed endpoint direction and cocartesian forward direction.
For an empty finite index the product-space construction is terminal and the
block test is an empty conjunction. The Day arity-zero fiber is a terminal product.
The containing universe can exceed both `u` and `u+1` independently.

Existing-declaration searches, using the prescribed `msearch.py N5
lem-coef-day-relative-exponential-model` interface:

- LeanFinder: `right fibrations target evaluation cartesian cocartesian Day convolution
  relative section classification`; eight ordinary Day-convolution/corepresentability
  results, no statement about the full quasicategory of right fibrations.
- Loogle: `SSet, CategoryTheory.MonoidalCategory`; zero results.
- Mathlib grep: `right.fibration|DayConvolution|relative.exponential` in `CategoryTheory`;
  21 ordinary Day-convolution results, no matching coherent RFib theorem.
- LeanSearch: `right fibration category of arrows target evaluation presheaves Day
  convolution`; eight ordinary Day-convolution results, no exact match.
- `rg` over the named upstream `WeilConjectures` tree and project `lean/Sheaf` for
  `CatInfinity`, `rightFibration`, `DayConvolution` and `relativeExponential`: the
  existing individual interfaces above were reused; no combined target statement.
  The exact item-id search in the upstream tree had no match. Ordinary Mathlib
  Day-convolution declarations were read and concern ordinary categories, so are not
  replacements for this node's statement.

The source check used Chu--Haugseng, arXiv:2006.08269, Notation 6.1, Proposition 6.2,
Lemma 6.9, Corollary 6.10, Remarks 6.11/6.15/6.17, Definition 6.14 and proof of
Proposition 6.18. Gepner--Haugseng--Nikolaus, arXiv:1501.02161, Definition 7.2 and
Proposition 7.3 identify the relative exponential's cartesian classifier and its
full section/evaluation interpretation. The node's ordered-block convention is kept.

The prescribed `scompile.py` compiled both delivered modules separately, including the
private prerequisite overlay and their final library paths: no errors or warnings,
with main library compilation approximately six seconds and the dependency repair
approximately three seconds (both below 60 seconds). No global build or direct Git
operation was run. The final delivery dry run performs the remaining required checks.

## Dependency modules

`lem-coef-space-valued-straightening` owns
`Sheaf.CategoryTheory.SpaceValuedStraightening`. The current live source was read with
`scompile.py --source Sheaf.CategoryTheory.SpaceValuedStraightening`. Its `Diagrams`
abbreviation used the now-noncomputable `smallSpaces` alias without a `noncomputable`
annotation. Rebuilding the required prerequisite closure failed with
`lean.dependsOnNoncomputable` at that abbreviation. This delivery changes precisely
`abbrev Diagrams` to `noncomputable abbrev Diagrams`. It preserves every construction,
all twelve declaration names, the complete theorem statement, and the existing source
and proof-plan docstrings. The dependency node copy changes only `lean`, with the
required explanation in `lean.note`; no other dependency field was changed.

## Second reading by N5

The dispatcher explicitly prohibited starting other agents; this section records a
separate self-review pass with the node and final modules open. It does not claim an
independent second worker. The maintainer's independent delivery review remains due.

The pass checked each clause above against the source statement and full signatures.
The singleton fiber comparison is fixed on every simplex, not only vertices. The
strong monoidal functor's actual coCart edge is identified before straightening, and
the induced opposite map is specified by cocartesian transport. The naturality square
uses its correct common domain, `Q_C' ×_S C^{op,⊗}`, with all four pullback projections
fixed. Only the ordered pullback is required to satisfy the envelope cocartesian
criterion. Empty products, tensor units, discarded coordinates and arbitrary
containing universes remain present. The spaces category is the existing
`smallSpaces = Spaces.infinityCategory` alias; no extra equivalence or substitute
spaces model is used. The dependency repair was reread: its only source change is the
noncomputable annotation, so its mathematical statement has not changed. No remaining
statement mismatch was identified in this reading.
