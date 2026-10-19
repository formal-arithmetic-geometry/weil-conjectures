## Worker report

`Sheaf.CategoryTheory.FinalSquareFullFaithfulness` states
`SSet.Enhanced.final_square_full_faithfulness`, with its sole proof `sorry`.
The mathematical statement is unchanged. No new nodes or dependency repairs are needed.
The already landed `lem-coef-infinity-colimit-gluing` is added to `stmt_deps`
for its existing canonical `gluingCoconeRestrict`; its whole gluing theorem is not assumed.

Source checked online: [Cisinski, CatLR](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
Corollary 7.5.17 and the proof of Theorem 7.5.18, printed pp. 379--380,
PDF pp. 394--395. The item abstracts its coherent square argument; it does not
assert the Brown theorem. Its given proof uses corepresentable comma colimits.

Hypothesis and clause correspondence:

- Small quasicategories: `{A B X Y : SSet.{u}}` and the four `Quasicategory` instances.
  All universes and variables are explicitly bound, with `autoImplicit false`.
- Coherent functors: `(i : A ⟶ B) (q : A ⟶ X) (r : B ⟶ Y) (u : X ⟶ Y)`.
- The specified coherent natural equivalence is a supplied edge
  `θ : ((ihom A).obj Y) _⦋1⦌`, with `hθsource`, `hθtarget`, and `hθequiv`.
  These are precisely the data existentially packaged by the recorded
  `AreNaturallyEquivalent (i ≫ r) (q ≫ u)` definition; exposing the edge lets
  the actual comma comparison refer to this same equivalence.
- `hi : IsFullyFaithful i` uses the dependency's realization weak equivalences
  on the right-pinched mapping spaces, not ordinary full and faithful functors.
- `hq` quantifies over every vertex `x` of `X`, and supplies `a` and an
  equivalence edge with source `q(a)` and target `x`. This is exactly the
  essential-surjectivity hypothesis, including its direction and inverse witnesses.
- `T a` has source `comma A X q (q.app _ a) true` and target
  `comma B Y r (u.app _ (q.app _ a)) true`. These are the recorded degreewise
  coherent arrow pullbacks, including their full higher simplices.
- The induced formula is specified in every simplicial degree. `hTind` makes
  the first coordinate `i(b)`. The simplicial triangle family `w a` has
  `01 = θ_b` by `hwθ`, `12 = u(α)` by `hwα`, and `02` equal to the actual
  second coordinate of `T a` by `hwT`. Thus `T a` is the coherent composite
  `u(α) θ_b`, with a whole triangle transformation, not independent pointwise
  homotopies. `yonedaEquiv.symm θ`, uncurrying, the symmetry, and currying
  turn the given transformation on `A` into its family of component arrows.
  `T,w` simply expose a representative of the induced functor and its
  composition witness; the theorem is universal over these representatives.
  An inner 2-horn in the functor quasicategory supplies such a composition;
  no extra property of the square is being imposed.
- `hT` is finality with exactly the node's definition. For every target
  quasicategory `E`, diagram `F`, and supplied colimiting cocone `c`, its
  actual restriction along the lifted `T a` is colimiting with the same apex.
  Target size is `max (u+1) v`; the lifted small comma sits in that universe.
  This includes the category of u-small spaces and allows arbitrary further
  enlargement, rather than testing only ordinary categories or small sets.
- The conclusion `IsFullyFaithful u` unfolds to every pair of vertices of
  `X` and the specified actual `mappingSpaceMap u x x'` being a weak homotopy
  equivalence. No existential unrelated equivalence of mapping spaces is used.

Recorded declarations read in full, with docstrings:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`,
  `diagramVertex`, `evaluation`, `mappingSpace`, `mappingSpaceMap`,
  `IsWeakHomotopyEquivalence`, `IsFullyFaithful`, `AreNaturallyEquivalent`,
  `commaSubcomplex`, `comma`, `coconeCategory`, `IsInitial`, `IsColimiting`.
- `Sheaf.CategoryTheory.InfinityColimitGluing`: `gluingCoconeRestrict`;
  it precomposes the whole coherent transformation and retains the apex literally.
- Non-public proof-plan imports are `EnhancedFunctorConeCalculus` and
  `InfinityMappingComposition`, the recorded modules of the corresponding
  proof dependencies. The corepresentable-colimit and Hom-bifunctor nodes
  currently have no recorded module; no substitute theorem is introduced.
- Mathlib's `SSet.Quasicategory` is the inner-horn filling class, and `ihom`
  and `SSet.uliftFunctor` are the existing simplicial internal-hom and lift APIs.

Edge cases checked: empty `A` forces empty `X` by `hq`, so full faithfulness
is vacuous. The identity square uses degenerate composition triangles and
identity comparisons. Empty comma categories and empty cocones are not
excluded. Nontrivial equivalences and automorphisms retain their inverse
triangles and all coherences. All four categories may be in universe zero;
the explicit `u+1` enlargement still includes their category of small spaces.
No finiteness, nonemptiness, completeness, ordinary-category, or characteristic
assumption is imposed. A groupoid `BG → point` cannot be mistaken for a fully
faithful map solely from ordinary connectedness: the mapping-space weak
homotopy equivalence and coherent finality tests retain that obstruction.

Searches actually run in this session:

- `msearch.py ... leansearch` query: “Final comma comparisons in a coherent
  square of quasicategories detect full faithfulness when the top functor is
  fully faithful and the left functor is essentially surjective”. Eight hits,
  including ordinary `Comma.isEquivalenceMap`, `CostructuredArrow.essSurj_map₂`,
  and `CatCommSq.iso`; no quasicategorical mapping-space criterion.
- `msearch.py ... leanfinder` query: “A coherent square of quasicategories with
  fully faithful top functor and essentially surjective left functor has fully
  faithful bottom functor when its comma comparisons are final”. Eight hits,
  including `TwoSquare.guitartExact_iff_final`, `CostructuredArrow.full_map₂`,
  and `Functor.final_of_comp_full_faithful`; all concern ordinary categories.
- `msearch.py ... loogle "CategoryTheory.Functor.Full, CategoryTheory.Functor.Final"`:
  four ordinary finality lemmas; no coherent square theorem.
- `msearch.py ... grep "GuitartExact|fullyFaithful.*Kan|Kan.*fullyFaithful"
  CategoryTheory`: 25 ordinary Guitart-exact/localization hits. Opened
  Mathlib `GuitartExact/Basic.lean` at its definition and finality criterion,
  and upstream `FromJoel/CategoryTheory/GuitartExact/Basic.lean`; they do not
  concern entire quasicategorical mapping spaces.
- `rg` across the specified `WeilConjectures/` source and shared `lean/Sheaf/`
  for the item, proposed declaration name, and `GuitartExact`: no exact
  statement; only ordinary-category Guitart-exact uses. Shared searches for
  `comma`, finality, and cocone restriction found the existing restriction
  helper, which is imported and cited rather than copied.

Validation: the delivered module is checked with `scompile.py`; the recorded
Lean signature is extracted verbatim from the module. The dry run is required
before the READY handoff. No statement dispute or node correction is needed.

## Second reading by NP

Read the base node and sandbox node against the complete module, independently of
the worker's correspondence. There is no maintenance repair note for this item.
The source is Cisinski's CatLR, July 30, 2026 revision, Corollary 7.5.17 and
Theorem 7.5.18, printed pp. 379--380 (PDF pages 394--395), opened online in this
reading. This item has no Stacks source. Corollary 7.5.17 obtains the canonical
base-change equivalence by finality of the comma comparison. The theorem then
combines this with full faithfulness of the upper inclusion and essential
surjectivity of the left localization to prove full faithfulness below. The node
explicitly abstracts that argument; the Brown-category hypotheses establish its
inputs in that application and are not hypotheses of this abstract criterion.

The node's object/hypothesis/conclusion list, with its Lean rendering and verdict:

1. Four small quasicategories in a common universe: `{A B X Y : SSet.{u}}`
   and exactly four `Quasicategory` instances, lines 68--69. Mathlib's class
   in `Quasicategory/Basic.lean:40--44` is the inner-horn condition, with no
   inhabitedness requirement. MATCH.
2. Coherent functors `i : A → B`, `q : A → X`, `r : B → Y`, `u : X → Y`:
   the four simplicial-map binders at line 70, with these exact domains and
   codomains. No ordinary-category instances are substituted. MATCH.
3. A specified coherent natural equivalence `ri ≃ uq`: `θ` is an edge of
   `(ihom A).obj Y`; `hθsource` fixes its source to `diagramVertex (i ≫ r)`,
   `hθtarget` fixes its target to `diagramVertex (q ≫ u)`, and `hθequiv`
   supplies both inverse triangles. Read `AreNaturallyEquivalent:224--228`
   and `IsEquivalenceEdge:43--46` in `EnhancedDiagramsCones`: these binders
   expose exactly the witness in that definition, so the same transformation
   is available when describing the induced comparison. MATCH.
4. Full faithfulness of `i`: `hi : IsFullyFaithful i`. Read
   `mappingSpace:159--199`, `mappingSpaceMap:203--215`,
   `IsWeakHomotopyEquivalence:93--96` and `IsFullyFaithful:219--220` in the
   dependency module. This tests the actual induced map on the node's whole
   right-pinched mapping spaces, by components and all positive based homotopy
   groups after realization. It is not a test only on homotopy classes. MATCH.
5. Essential surjectivity of `q`: `hq` quantifies over every vertex of `X`,
   then supplies a vertex of `A` and an equivalence edge from its q-image to
   that vertex. Invertibility makes this direction equivalent to the node's
   phrase "equivalent to"; no simultaneous functorial choice is demanded. MATCH.
6. The two comma categories for each `a`: the `T` binder uses
   `comma A X q (q.app _ a) true` and
   `comma B Y r (u.app _ (q.app _ a)) true`. Read
   `commaSubcomplex:240--263` and `comma:267--268`: `true` imposes source
   equal to the functor image and target equal to the specified constant
   vertex in every degree. This is the displayed arrow pullback, retaining
   all its higher simplices. MATCH.
7. The induced comparison sends `(b,α)` to `(i(b),u(α)θ_b)`: `hTind` fixes
   its first projection as a whole simplicial map. `w a` is a whole simplicial
   family of triangles; `hwθ`, `hwα`, `hwT` fix its faces `01`, `12`, `02`,
   respectively. Uncurrying `yonedaEquiv.symm θ`, then applying the symmetry
   and currying, gives exactly the component-arrow family `A → Fun(Δ¹,Y)`.
   Pulling it back to the comma index gives `θ_b`, with no reversal. Thus the
   triangle expresses the required order `u(α) ∘ θ_b` on all parameters.
   This does not posit an unrelated arbitrary map or only vertexwise
   composition. Composition representatives exist by filling the inner
   2-horn in the functor quasicategory on the comma index; its long edge and
   the fixed first projection give `T`. Hence supplying `T,w` with these
   equations adds choices of representatives, not a restriction on squares.
   The universal theorem covers every such representative. MATCH.
8. Every comparison is final: `hT` ranges over each `a`, each target
   quasicategory `E`, each diagram `F` on the lifted target comma, and each
   supplied cocone `c`, and requires colimitingness after actual restriction
   whenever `c` was colimiting. Read `coconeCategory:278--279`,
   `IsInitial:293--294`, `IsColimiting:303--304`, and the complete construction
   `gluingCoconeRestrict:39--92` in `InfinityColimitGluing`. Restriction
   precomposes the transformation, with its apex coordinate literally
   unchanged. I removed the redundant apex equation from `hT`: the node's
   same-apex clause is already rendered by this exact restriction construction.
   It follows definitionally, so requiring it again as a conjunct violates the
   convention against tautological conjuncts. No existence of colimits in `E`
   is assumed. MATCH after this representational repair.
9. Size of the finality tests: `E : SSet.{max (u + 1) v}` with the index
   lifted by Mathlib's `uliftFunctor` (`SimplicialSet/Basic.lean:73--74`).
   The common containing universe includes the infinity category of
   u-small spaces needed in the node's proof, and `v` permits further
   enlargement. Smaller targets can be lifted to it. The four original
   categories have no extra universe equality beyond the node's common
   fixed universe. No site-universe or coefficient restriction appears. MATCH.
10. Conclusion for every pair `x,x'` of `X`: `IsFullyFaithful u` unfolds to
    `∀ x y, IsWeakHomotopyEquivalence (mappingSpaceMap u x y)`. This is the
    specified induced map, not an existential equivalence between unrelated
    spaces, and no conclusion about essential surjectivity of `u` is added.
    The order of all hypotheses and choices leaves finality as a hypothesis
    on the same `T` whose induced-map equations were supplied. MATCH.

Also opened the statement and recorded declarations of each dependency.
`lem-coef-infinity-colimit-gluing` supplies the canonical restriction helper;
its gluing theorem is not a hypothesis here. The non-public imports
`EnhancedFunctorConeCalculus` and `InfinityMappingComposition` match the
recorded proof dependencies: their signatures provide componentwise
equivalences, the cocone initial-object criterion, and the specified coherent
composition/identity/inverse-triangle package. Read those signatures and their
defining predicates. The corepresentable comma-colimit and Hom-bifunctor
proof dependencies have no recorded Lean module in the base, so there is no
missing available proof import to add. No new definition node or dependency
module is part of this delivery; there is no private copy or hollow definition.

Edge cases: if `A` is empty, `hq` forces `X` empty, and the conclusion has no
pairs to test. Empty comma categories, empty mapping spaces, and empty targets
are not excluded. With `A` a point and `i = q = id`, finality of the specified
comparison detects whether the actual endomorphism space below is contractible;
it does not collapse a nontrivial groupoid to its connected components. Identity
squares use degenerate triangles. Nonidentity equivalence components retain
both inverse triangles. Universe `u = 0` is included, and the containing
universe is still large enough for small spaces. There are no schemes, rings,
characteristic, integer-degree, or zero-object hypotheses in this node; no
such edge case has been introduced or excluded by the Lean.

Independent searches in this second reading (actually run through `msearch.py`):

- LeanFinder: "Homotopy cofinal functors between comma infinity categories
  detect fully faithful functors in a naturally commuting square". Eight
  hits, including `TwoSquare.guitartExact_iff_final`,
  `CostructuredArrow.full_map₂`, ordinary cocone functoriality, and model-category
  homotopy/localization statements. None is this theorem.
- LeanSearch: "Full faithfulness of a simplicial map between quasi categories
  follows from cofinal induced over category maps and a full faithful
  essentially surjective square". Eight hits: ordinary induced categories,
  `CostructuredArrow.essSurj_map₂`, full faithfulness of the nerve functor,
  and skeleton/truncation functors. None asserts this mapping-space criterion.
- Loogle: `"Quasicategory", "FullyFaithful"`. Zero hits.
- Grep via the wrapper: `cofinal.*faithful|final.*fully|fully.*final` in
  `AlgebraicTopology`. Zero hits.
- Direct `rg` in the specified upstream `WeilConjectures`, shared `lean/Sheaf`,
  and Mathlib for `cofinal.*faithful|final.*fully|fully.*final`, and searches
  for `final_square_full_faithfulness`/the item id, found no duplicate.
  Also checked `dag/lean_names_upstream.json` for the name and id. Opened
  Mathlib `CategoryTheory/GuitartExact/Basic.lean:51--62,223--268`: the
  candidate uses ordinary categories and connected ordinary comma categories,
  so it cannot replace this quasicategorical statement. The project's
  `InfinityCofinalCommaCriterion` and `InfinityRightAdjointReindexing`
  signatures were also opened: they provide other finality criteria or
  reindexing statements, not this square criterion.

Mismatches and changes: the mathematical statement matches. One redundant
conjunct required the apex equality that `gluingCoconeRestrict` already supplies
definitionally. Removed that conjunct from `hT`, preserving the same-apex
condition through the canonical map, and updated `lean.statement` verbatim.
This is a representational cleanup, not a mathematical statement correction.
The dependency addition for the existing canonical restriction helper is
appropriate. The declaration docstring carries all five
proof steps with their cited nodes, and both docstrings carry the source and
blueprint id. The only proof is the named theorem's `sorry`. No file-local
notation, local instances, private definitions, hidden `let`/`show` statement
terms, or unbound variables/universes occur. The recorded `lean.statement`
was checked byte-for-byte against the source signature.

Validation: the revised sole delivered file passed `scompile.py`, both the
sandbox and library checks, cleanly (1.9 s and 2.0 s). The fresh
`deliver2.py NP lem-coef-final-square-full-faithfulness --no-push` returned
`OK (dry run)` with server preflight and compilation passing. An earlier
invocation had captured the old recorded signature before the cleanup; the
fresh invocation checks the final, byte-for-byte matching signature and node
record. No read-only project source or direct git operation was modified.
