## Worker report

`Sheaf.CategoryTheory.PointedModelStability` states
`HomotopicalAlgebra.PointedModel.pointed_model_category_stability`. Its one theorem
has proof `sorry`; every helper has actual defined data. This replaces the earlier
sandbox attempt, whose ordinary-only localization, arbitrary finite "square", unconnected
pushout witness, and unrelated suspension/loop functors did not state the node.

The authoritative statement and nine proof steps are unchanged. The theorem follows
"Let M_infinity be the homotopy coherent localization": it accepts the localization
`C`, its map `q`, and the published `FiniteReedy.IsLocalization` predicate. It does
not add a theorem asserting existence of a localization, which the node did not assert.
The returned zero object is the actual vertex `object q (0 : M)`.

Hypothesis and clause correspondence:

- `M : Type u` and `[Category.{v} M]` are the ordinary category, with object and
  morphism universes independent. `[HasLimits M] [HasColimits M]` express completeness
  and cocompleteness, including the finite limits/colimits in the recorded dependency.
- `[HasZeroObject M]` is the pointedness assumption. Mathlib's existing `ZeroObject`
  scope supplies the conventional notation; no notation is introduced by this module.
- `[ModelCategory M]` supplies the three actual morphism properties. I read the full
  definition: `cm2` is two-out-of-three, `cm3a` retract closure of weak equivalences,
  `cm4a/b` lifting, `cm5a/b` the two factorizations. The immediately following instances
  give both weak factorization systems, including their lifting-class characterizations.
  `trivialCofibrations` and `trivialFibrations` mean the intersections with weak equivalences.
- The two explicit `MorphismProperty.HasFunctorialFactorization` binders retain
  functoriality for both pairs; plain `ModelCategory` alone would not retain it.
  `IsCofibrant` in the pushout helper is Mathlib's initial-to-object cofibration;
  initial and zero agree in this pointed category.
- `C : SSet.{max u v t}` and `q : largeNerve M ⟶ C` permit a larger localization
  universe. `FiniteReedy.IsLocalization (weakEquivalences M) q` includes
  `C.Quasicategory`, equivalence-edge inversion, and the entire coherent functor-category
  universal property, including coherent transformations and higher simplices. Its
  precomposition equivalence is required to factor the actual precomposition map.
  It is not an ordinary localization predicate or an unconstrained Prop field.
- The first two conclusion conjuncts assert that `q(0)` is initial and terminal in
  the mapping-space sense of `SSet.Enhanced.IsInitial` and `IsTerminal`.
- The next two conjuncts quantify over every `K.Finite` and every simplicial map
  `F : K ⟶ C` and supply respectively a limiting cone and colimiting cocone in the
  dependency's actual comma categories. This is finiteness of nondegenerate simplices,
  not finiteness of a category in `hC`.
- `HasOrdinaryLocalizationComparison M q` gives an actual ordinary localization
  `Q : M ⥤ hoFunctor.obj C`, using Mathlib `Functor.IsLocalization`, and requires
  equality on every simplex with `q` followed by `nerveAdjunction.unit.app C`.
  `Q.mapComposableArrows` expresses this comparison without silently equating the
  category universes. The ordinary localization therefore refers to the same `q`.
- `ComputesCofibrantPushouts M q` quantifies over all three cofibrant objects and both
  cofibration legs and every ordinary colimiting cocone on that span. It requires
  `IsColimitEdge` of its actual localized diagram, actual localized apex and actual
  localized cocone transformation. No unrelated coherent pushout can witness this clause.
- `HasSuspensionLoop z suspension loop` requires coherent simplicial endofunctors.
  Its suspension-square family has vertices `(x,z,z,suspension x)` and is pointwise
  a coherent pushout; its loop-square family has vertices `(loop x,z,z,x)` and is
  pointwise a coherent pullback. The four equations are equations of simplicial maps,
  so all transformations and higher compatibility simplices are retained.
- `IsAdjunction suspension loop` gives a coherent unit from identity to the composite.
  At each `x`, that precise unit with apex `suspension x` is initial in the coherent
  comma category of arrows `x → loop y`. This is the universal-arrow definition of
  an infinity-categorical adjunction, including the mapping-space universal property.
- The final implication assumes only that `(hoFunctor.map suspension).toFunctor`
  is an equivalence of ordinary categories. It concludes, for every coherent square,
  `IsPushoutSquare s ↔ IsPullbackSquare s`. The implication remains conditional;
  stability of arbitrary pointed model categories is not asserted.

Square implementation: `squareShape` is the degreewise-lifted nerve of the ordered
product `Fin 2 × Fin 2`. This is the product of two interval nerves, hence the usual
coherent-square shape. `spanInSquare`, `cospanInSquare`, `squareCocone`, and `squareCone`
are explicit ordinary diagram data, with their order arrows. The two square predicates
apply `diagram`, `object`, and `transformation` to those fixed data and the SAME square
map. `IsColimitEdge` and `IsLimitEdge` then test the specified dependency cocone/cone.
A general finite diagram with unrelated cone and cocone is no longer a square.
The helper definitions are constituents of this node's notions, not independent DAG
statements, and are all listed in `lean.declarations` with source/blueprint docstrings.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits`:
  `CategoryTheory.Limits.HasFiniteLimits`, `HasFiniteColimits`, and the instances from
  completeness/cocompleteness. These are already public imports through the model API.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: read its whole source, including
  `IsEquivalenceEdge`, `mappingSpace`, `mappingSpaceMap`, `IsFunctorEquivalence`,
  `diagramVertex`, `evaluation`, `comma`, `coneCategory`, `coconeCategory`,
  `IsInitial`, `IsTerminal`, `IsLimiting`, `IsColimiting`. These are imported through
  the publicly imported Reedy module; no private copy of those notions is made.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`: read its whole source. Its owning
  proof-dependency node is now also a statement dependency because its grounded
  helper interface `largeNerve`, `IsLocalization`, `object`, `diagram`,
  `transformation`, `IsColimitEdge`, and `IsLimitEdge` is used in the signature.
  This adds only an already-landed node, as permitted by brief-stage2 section 5.
  I checked there is no dependency path from the Reedy node back to this item.
- `Sheaf.AlgebraicTopology.InfinityFiniteShapeGeneration` is imported for the proof
  plan, without `public`; I read its finite-shape signature and proof docstring.
  `lem-coef-suspension-square-comparison` has no Lean record and is omitted from
  imports, as it is only a proof dependency. Its proof role is fully retained in the
  theorem docstring. No other DAG theorem is stated in this delivery.
- Mathlib `nerveAdjunction`, `hoFunctor`, `SSet.Finite`, `Functor.IsLocalization`,
  model-category axioms, ordinary span/cospan and cone/cocone APIs are used directly.

Edge cases checked before and after writing:

- Empty finite simplicial shapes are included with no nonemptiness binder; these
  yield the same zero object. Arbitrary finite higher simplices are included as well.
- The zero category and identity/zero-map spans satisfy the same formulas. No
  nonzero-object, properness, simplicial-model-category, or stability hypothesis was added.
- A nonstable pointed model category still satisfies the unconditional localization,
  finite-shape and adjunction clauses; the last implication requires suspension to be
  an equivalence and need not apply (e.g. pointed spaces).
- The cofibrant-span clause quantifies over all ordinary pushout cocones and connects
  the exact cocone, rather than just its apex, to the coherent colimit.
- Square coordinates agree in both predicates: W=(0,0), X=(1,0), Y=(0,1), Z=(1,1).
  Both predicates test the same square and its compatibility homotopies.
- Universe variables `u v t` are explicit, autoImplicit is disabled, and localization
  size is `max u v t`. No universe equality is imposed to use the ordinary comparison.

Searches in this pass (2026-10-16):

- `msearch.py ... leanfinder "Pointed model category homotopy coherent localization
  finite homotopy limits suspension loop adjunction stability"`: eight hits on
  cofibrant-object homotopy/localization, none the coherent statement.
- `msearch.py ... loogle '"ModelCategory", "Suspension"'`: zero hits.
- `msearch.py ... leansearch "homotopy coherent model category localization suspension
  loop adjunction stability"`: eight hits on ordinary localization adjunctions,
  model-category constructors and cofibrant homotopy, no statement match.
- `msearch.py ... grep 'StableModel|stableModel|[Ss]uspension.*[Mm]odel|[Mm]odel.*[Ss]uspension'
  CategoryTheory`: zero hits. The same `rg` over all Mathlib, upstream `WeilConjectures`
  and project `lean/Sheaf` also returned no match.
- `rg` for the item id in upstream `WeilConjectures`: no match. A search for the
  actual helper/declaration names over Mathlib, upstream and project sources found
  no duplicate. `dag/lean_names_upstream.json` also has no pointed-model match.
- Read the current published owning nodes and their actual modules, not stale sandbox
  or name-only interfaces. No new independent definition node was needed.

Source check: opened the archived blueprint proof paragraph 2. Also opened
https://people.math.harvard.edu/~lurie/papers/HA2012.pdf at Proposition the project server,
Lemma the project server, and Corollary the project server. These retain the coherent square and conditional
suspension/loop criterion; no source-based statement correction is needed.

Validation: `scompile.py NK lem-coef-pointed-model-stability <module>` succeeded for
both sandbox and module import, with no errors or warnings. The theorem is the only
postponed proof and its docstring carries all nine DAG proof steps and references.

## Second reading by NK

I independently opened the authoritative node, its sandbox copy and the complete
`PointedModelStability.lean`, then followed the definitions used in its signature.
Verdict: the current module says what the node says. I found no remaining mismatch
and changed no Lean declaration or node field; this section is the delivery change
made by the second reader. The worker's account of an earlier sandbox attempt is
not evidence for this verdict: I reviewed the current definitions themselves.

Objects, hypotheses and conclusion, matched in the order of the node:

1. The complete and cocomplete ordinary category is `(M : Type u) [Category.{v} M]`
   with `[HasLimits M] [HasColimits M]`. These are Mathlib's small completeness
   conventions (`HasLimitsOfSize.{v,v}` and its dual), with independent object and
   morphism universes. The finite ordinary limits and colimits cited by
   `def-galois-finite-limits-colimits` are the existing Mathlib classes, inherited
   through the model API; their definitions agree with Stacks `categories.tex`,
   section `section-finite-limits` (04AS), which I opened. No finite-shape
   hypothesis on M replaces the node's completeness assumption. PASS.
2. The zero object is `[HasZeroObject M]`; the localized zero is explicitly
   `object q (0 : M)`. I checked that this is evaluation of q on the zero object's
   actual nerve vertex. PASS.
3. The model structure is `[ModelCategory M]`. I opened Mathlib's class and the
   two immediately following weak-factorization-system instances: its stored
   classes, two-out-of-three, retract closure, lifting and factorizations supply
   exactly the model structure described by the node. The additional two
   `MorphismProperty.HasFunctorialFactorization` instances concern precisely
   `(trivialCofibrations M, fibrations M)` and
   `(cofibrations M, trivialFibrations M)`. They retain the node's explicit
   functoriality requirement, absent from bare `ModelCategory`. PASS.
4. The supplied homotopy coherent localization is `C : SSet.{max u v t}` and
   `q : largeNerve.{u,v,t} M ⟶ C`, with
   `FiniteReedy.IsLocalization (weakEquivalences M) q`. I read `largeNerve`,
   `Inverts`, `localDiagrams`, `comparison` and `IsLocalization` in the landed
   `FiniteReedyLocalization.lean`: C is a quasicategory, q inverts the weak
   equivalences, and actual precomposition is an equivalence onto the full
   coherent functor subcategory of inverting diagrams. This includes higher
   simplices. The node says to let the localization be given, so hq correctly
   specifies it rather than adding or claiming its existence. PASS.
5. A zero object of C is asserted by the first two conjuncts,
   `SSet.Enhanced.IsInitial C (object q (0 : M))` and its `IsTerminal` analogue.
   I read both predicates down to contractibility of their actual right-pinched
   mapping spaces in `EnhancedDiagramsCones.lean`. PASS.
6. Finite homotopy limits and colimits are the next two conjuncts: for every
   `K : SSet.{max u v t}`, proof of `K.Finite`, and `F : K ⟶ C`, a vertex of
   the dependency's `coneCategory F` or `coconeCategory F` is limiting or
   colimiting. I checked `commaSubcomplex`, `comma`, both cone categories,
   `IsLimiting` and `IsColimiting`; these use simplicial endpoint equations and
   mapping-space universal properties. `K.Finite` counts nondegenerate simplices,
   as in the node's finite homotopy-shape convention. PASS.
7. The ordinary homotopy-category comparison is
   `HasOrdinaryLocalizationComparison M q`. Its witness is an ordinary functor
   `Q : M ⥤ SSet.hoFunctor.obj C` satisfying Mathlib's `Q.IsLocalization W`.
   I opened that class and the nerve adjunction: the further equality for every
   degree and every nerve simplex identifies Q with q followed by the canonical
   nerve-adjunction unit. Thus this is the ordinary localization of the same
   category at the same W and the same q, not an unrelated localization. PASS.
8. Ordinary computation of the specified homotopy pushout is
   `ComputesCofibrantPushouts M q`. It quantifies over A, B, D, i and j, then
   their three cofibrancy assumptions, both cofibration assumptions, and every
   ordinary colimiting cocone s on `span i j`. I checked Mathlib's
   `IsCofibrant X = Cofibration (initial.to X)`; initial and zero objects are
   canonically isomorphic here. The conclusion applies `IsColimitEdge` to the
   exact `diagram q (span i j)`, `object q s.pt` and `transformation q s.ι`.
   I opened those three constructions and `IsColimitEdge`: both apex and
   coherent cocone are fixed, so a witness cannot substitute another span or
   another cocone. PASS.
9. Suspension and loop are the existential simplicial endofunctors
   `suspension loop : C ⟶ C`. In `HasSuspensionLoop`, their coherent square
   families S and T have evaluations `(x,z,z,suspension x)` and
   `(loop x,z,z,x)`, respectively, and their actual square maps satisfy
   `IsPushoutSquare` or `IsPullbackSquare` at every x. The four evaluation
   equalities in each family hold as simplicial maps, so they retain naturality
   and higher compatibility. This expresses the functorial homotopy
   constructions in the node. PASS.
10. The suspension-loop adjunction is the final conjunct of
    `HasSuspensionLoop`, namely `IsAdjunction suspension loop`. Its witness η
    is a coherent transformation from identity to `suspension ≫ loop`, and
    its component at x, with apex `suspension x`, is initial in the actual
    comma category `(x ↓ loop)`. I checked that the Bool argument `false`
    in the dependency indeed gives arrows from x to `loop y`, rather than
    the opposite direction. This is the universal-arrow formulation of the
    infinity-categorical mapping-space adjunction. PASS.
11. Finally the equivalence assumption is exactly
    `(SSet.hoFunctor.map suspension).toFunctor.IsEquivalence`. Under this
    assumption, every `s : squareShape ⟶ C` satisfies
    `IsPushoutSquare s ↔ IsPullbackSquare s`. I checked the ordered product
    `Fin 2 × Fin 2`, both span and cospan inclusions, and their actual cone
    and cocone: the vertices are W=(0,0), X=(1,0), Y=(0,1), Z=(1,1).
    Both predicates use the same coherent square, with its diagonal and
    triangle data, restricted to these fixed diagrams. The equivalence is
    conditional on hΣ being an equivalence; no stability of all pointed
    model categories is asserted. PASS.

Source review: I opened the archived blueprint proposition, especially proof
paragraph 2 and its displayed derived-Hom computation. As the node itself says,
this generic model-category foundation is agent-formulated; there is no Stacks
tag for it. I also independently opened Lurie's August 2012 Higher Algebra at
[Proposition the project server and Corollary the project server](https://people.math.harvard.edu/~lurie/papers/HA2012.pdf),
printed pp. 117 and 122. Their hypotheses are pointedness and finite homotopy
(co)limits, and the suspension/loop criterion is coherent. The extra passage
from equivalence of hΣ follows from the adjunction's unit/counit as spelled out
in DAG step 6 and the theorem docstring; it is not falsely quoted as a verbatim
claim of Lurie. No hidden properness, combinatoriality, simplicial model
structure, field or characteristic assumption has been introduced.

Dependency and packaging review: all three statement dependencies were opened
as nodes and their recorded definitions were read. The added statement
dependency `lem-coef-finite-reedy-localization` already has its landed Lean
record; using its grounded helpers is authorized by section 5 of the brief.
`EnhancedDiagramsCones` is publicly imported by that dependency, including the
recorded ordinary finite-limit API through Mathlib's model API. I also opened
the stated proof dependency `InfinityFiniteShapeGeneration.lean`: its finite
shape binders and cone predicates are precisely those used here. The remaining
proof-only suspension-square comparison has no Lean record and is correctly
left to the proof docstring. No new definition node or dependency repair module
is present or needed. The only changes from the authoritative node are `lean`
and the one added landed `stmt_deps` entry; there is no statement correction
requiring a citer audit.

Edge cases: the empty finite simplicial set is included without a nonemptiness
assumption and supplies the initial/terminal cases. Degree zero and higher
finite shapes are included. The trivial category, zero objects, identity legs
and zero legs are not excluded; cofibration legs retain precisely the stated
conditional requirement. A nonstable pointed category is covered by the
unconditional conclusions while the last implication need not apply. Empty
schemes, numerical n and characteristics introduce no additional hypotheses in
this abstract category-theoretic node. The universes u, v and t are bound
explicitly; q's nerve and C share `max u v t`, without equating u and v.
The ordinary comparison uses `mapComposableArrows` to avoid such an equality.
Square shapes are lifted from their finite small category, so that their
size does not restrict C. No auto-implicit variable is needed.

Independent searches (second reader):

- `msearch.py ... leanfinder "quasicategory pointed model homotopy localization
  suspension loop stable category"`: eight hits, principally Mathlib's
  truncated homotopy category and `SSet.hoFunctor`, no statement match.
- `msearch.py ... loogle '"Quasicategory", "ModelCategory"'`: zero hits.
- `msearch.py ... leansearch "a pointed model category localization is a stable
  infinity category if suspension on its homotopy category is an equivalence"`:
  eight hits on ordinary model homotopy/localization and triangulated
  localizations, none this coherent statement.
- Independent `rg` of Mathlib's algebraic topology and category theory, upstream
  `WeilConjectures` and project `lean/Sheaf` for `stablemodel`, `stable_model`,
  pointed/model phrases, `IsAdjunction`, `HasSuspensionLoop`,
  `IsPushoutSquare`, `IsPullbackSquare`, and suspension/loop phrases found no
  reusable version of this statement or these missing coherent helper notions.
  Other pointed models were algebraic-geometric models; ordinary adjunctions
  act on ordinary categories, and the landed Reedy adjunction helpers concern
  constant-diagram functors rather than arbitrary endofunctors. The upstream
  name inventory has no pointed-model entry. I retained the existing coherent
  cone, localization, ordinary homotopy-category and model-category APIs.

H5/H6/H8/H9 checks: every helper has actual constructed data or an explicit
Prop-valued formula; no data are chosen from an unproved existence statement.
The only theorem is `pointed_model_category_stability`, with proof `sorry`.
All declarations have source/blueprint docstrings and are in the node's
`lean.declarations`; the theorem docstring retains all nine DAG proof steps.
There is no private definition, custom local notation or instance, hidden
statement `let`, unbound variable, or line longer than 100 characters. I
checked by exact string comparison that `lean.statement` is the signature
from `theorem` up to `:= by`, with identical newlines.

Validation: the required `scompile.py NK lem-coef-pointed-model-stability`
invocation compiled the delivered module both as sandbox input and under its
library module name, with no errors or warnings (31.8 s and 16.5 s).
