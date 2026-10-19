## Worker report

The delivery states the bounded-below classical comparison in
`lean/Sheaf/AlgebraicGeometry/ClassicalDerivedEquivalence.lean`.
`AlgebraicGeometry.ProEtale.IsClassicalModuleFor` renders classicality of a
module sheaf by invertibility of the canonical continuity map on every affine
pro-etale presentation. `IsClassicalComplexFor` requires this for every derived
cohomology sheaf, and `ClassicalPlus` is the corresponding object property on
`DerivedCategory.Plus`.

The main theorem is
`AlgebraicGeometry.ProEtale.classicalDerivedEquivalence`. Its hypothesis
`hunit` quantifies over every bounded-below etale derived object and states that
the unit of
`(comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus` is an isomorphism.
The first conclusion quantifies over every such object and says that
`comparisonUpperStar.mapDerivedCategoryPlus` lands in `ClassicalPlus`; this is
clause (1)'s inverse-image assertion. The right adjoint in the displayed
`derivedPlus` has codomain `DerivedCategory.Plus` by construction, so its
bounded-below preservation is represented by its typed codomain. The second
conclusion quantifies over every bounded-below pro-etale object with classical
cohomology and states that the counit is an isomorphism, which is clause (2).
The final conclusion is a `Nonempty` categorical equivalence between the etale
bounded-below category and the full subcategory cut out by `ClassicalPlus`,
rendering the final inverse-equivalence assertion.

The remaining hypotheses are rendered without finiteness or separation
conditions: `X : Scheme.{u}` is an arbitrary scheme; `Λ : Type (u + 1)` and
`[CommRing Λ]` give the commutative coefficient ring in the common larger
universe; `[TopologicalSpace Λ] [DiscreteTopology Λ]` state exactly its
discreteness. The comparison constructions themselves only use its ring
structure. The quantifiers in `hunit`, the inverse-image clause, and the counit
clause range over all bounded-below objects, with no fixed lower bound.
`IsClassicalModuleFor` requires `IsIso (continuityMap P F.obj)` for every
`AffinePresentation`, and `IsClassicalComplexFor` requires it for every
`q : ℤ`; `ClassicalPlus` applies this predicate to `DerivedCategory.Plus.ι`.
Thus the full subcategory has precisely the classical cohomology condition.

The module imports the published comparison framework
`WeilConjectures.SixFunctors.ProEtale.Derived.Comparison` and the published
continuity-map framework
`Sheaf.AlgebraicGeometry.ClassicalContinuityMap`. The latter supplies
`AlgebraicGeometry.ProEtale.AffinePresentation` and
`AlgebraicGeometry.ProEtale.continuityMap`, used directly in the generalized
coefficient-category predicate. The comparison functors are
`AlgebraicGeometry.ProEtale.comparisonUpperStar`,
`comparisonAdjunction`, and its `derivedPlus` construction.

## Dependency modules

The dependency `sk-def-pe-classical-definition` currently records the existing
`Sheaf.AlgebraicGeometry.ClassicalContinuityMap` declarations. Its module-sheaf
predicate takes intrinsic modules over the constant sheaf of a lifted ring,
whereas the recorded `sk-prop-sf-comparison` uses `Sheaf ... (ModuleCat Λ)`
with `Λ : Type (u + 1)`. That interface cannot be applied to the comparison's
cohomology sheaves. The delivered dependency module
`Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions` supplies
`IsClassicalModuleFor` and `IsClassicalComplexFor` in this coefficient category,
and `ClassicalPlus` for its bounded-below full subcategory. It imports and
reuses the published `AffinePresentation` and `continuityMap` constructions;
the original set-sheaf and intrinsic module predicates remain reexported.
The copied dependency record changes only its `lean` field and explains this
interface repair. These are real predicates, with no postponed data or proofs.

The remaining recorded statement interfaces are:

- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`,
  `AlgebraicGeometry.ProEtale.boundedBelowComparison`: its unit uses precisely
  `(comparisonAdjunction (ModuleCat Λ) X).derivedPlus`, as does `hunit` here.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `AlgebraicGeometry.Scheme.proEtaleSiteComparison`: the same site inclusion
  and left Kan extension/sheafification construction used by
  `comparisonAdjunction`, specialized to coefficient modules.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: the intrinsic module encoding, reexported
  by `ClassicalContinuityMap`; the fixed-ring comparison uses the equivalent
  sheaves-of-modules encoding already used by `boundedBelowComparison`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, with
  `DerivedCategory.homologyFunctor` from `HomologySequence`: localization and
  every integer-degree cohomology functor.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
  `DerivedCategory.Plus`: the full subcategory defined by the existence of a
  lower cohomological bound, not a bound on the terms of a chosen complex.

## Edge cases checked

I checked that the predicates quantify over every integer cohomological degree,
that the zero module sheaf satisfies the continuity condition, that the empty
scheme is allowed by `Scheme`, and that the zero ring and zero derived object
remain admitted by `[CommRing Λ]` and the category definitions. The index type
for presentations is `Type (u + 1)`, matching the common larger site universe;
no lower independent universe is introduced. The bounded-below category uses
Mathlib's `DerivedCategory.Plus`, so arbitrary lower bounds and all shifts are
included.

## Searches

- `msearch.py ... leanfinder "bounded below derived equivalence between etale sheaves and proetale complexes with classical cohomology"`: no matching declaration; hits were generic derived-category or condensed-site declarations.
- `msearch.py ... loogle "DerivedCategory.Plus, comparisonAdjunction, ObjectProperty.FullSubcategory"`: no result (`comparisonAdjunction` is not in the Loogle identifier index).
- `msearch.py ... grep "classical|ClassicalPlus|derivedComparison" AlgebraicGeometry`: only unrelated Mathlib hits; the project hit was the continuity-map framework.
- `msearch.py ... leanfinder "classicality of cohomology sheaves on the small pro-etale site"`: no matching classical derived-equivalence declaration; only generic sheaf-cohomology declarations appeared.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/`: no existing declaration named `det-pe-classical-derived-equivalence`, `ClassicalPlus`, `IsClassicalModuleFor`, or `IsClassicalComplexFor`; the existing `ClassicalContinuityMap` declarations were read and reused.
- The node source and proof were read from
  `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-cor-pe-classical-derived/`.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

## Resumed worker self-check

The saved report was read first and the prescribed `deliver2.py --no-push`
dry run was started on the saved packet. Both delivered modules passed its
file-by-file compilation. The current blueprint detail and definition unit,
every current statement-dependency record, and the declarations behind the
comparison adjunction and `derivedPlus` were read. The saved report's obsolete
claim that no classicality interface was recorded has been corrected above.
No theorem statement or predicate data was changed by this report repair.

The copied records were repaired to include `existing: false` and verbatim
signatures; the dependency's primary declaration is now the declaration
actually defined in its delivered module, `IsClassicalModuleFor`, rather than
the imported `IsClassical`. Both JSON files differ from the current repository
only in `lean`. All declaration lines are at most 100 characters, every
universe and variable is explicitly bound, the definitions contain no proof
holes, and the sole postponed theorem is `classicalDerivedEquivalence`.

The theorem docstring now follows all eight DAG proof steps and names their
dependencies. The stated proof-dependency modules are imported without
`public`; the statement dependencies are available through public imports.
A direct import of `BoundedBelowProEtaleComparison` was tested and rejected
by the compiler because its lower-shriek import duplicates
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` from
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`.
Following the launcher's duplicate-import repair instruction, the consumer
instead imports the smaller upstream `Derived.Comparison` module, which gives
the identical comparison adjunction and `derivedPlus` used in the recorded
unit theorem. No comparison or derived functor is copied.

After that repair, the prescribed `scompile.py Q116
det-pe-classical-derived-equivalence <definitions.lean> <equivalence.lean>`
completed successfully for both files, including their separate library
compilations, with no errors or warnings. The named theorem remains `sorry`,
as required at stage 2.

## Second reading by Q116

I independently read the item node, both delivered modules, the six statement-dependency
records and their declarations, and the dependency definition node. The source read was
main-20261015, `sec-proetale-coefficients/sk-cor-pe-classical-derived/`:
`sk-cor-pe-classical-derived-equivalence.md`, its four-paragraph proof, and `_section.md`.
I also read `sk-def-pe-classical-definition/_section.md`. These sources put no finiteness,
Noetherian, separatedness, torsion, characteristic or cohomological-dimension assumption
on this conditional bounded-below equivalence. For the ambient site/module input I read
Stacks `proetale.tex`, Tag 099R (`section-comparison`, opening choices of sites),
099T (`lemma-fully-faithful`) and 099V (`lemma-relative-comparison`), and
`sites-modules.tex`, 03DA/03DB (`lemma-abelian`, `lemma-limits-colimits`). For the
lower-bound and truncation behavior I read `derived.tex`, 05TC (`lemma-negative-vanishing`).

The following is my item-by-item statement inventory and Lean correspondence, after repair.

1. An arbitrary scheme X: `(X : Scheme.{u})`. There is no extra geometric instance.
   Verdict: exact, including the empty scheme.
2. A discrete commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]
   [TopologicalSpace Λ] [DiscreteTopology Λ]`. The common larger coefficient universe
   is the one used by the recorded comparison theorem. ModuleCat uses discrete scalar
   actions; the auxiliary discrete topology does not introduce continuity or finiteness
   restrictions. Verdict: exact, including infinite rings and the zero ring.
3. The small etale and pro-etale sites and their comparison: respectively
   `X.smallEtaleTopology` and `Scheme.ProEt.topology X`, with
   `comparisonUpperStar (ModuleCat.{u + 1} Λ) X` and `comparisonLowerStar ... X`.
   I read `ProEtaleSiteComparison.proEtaleSiteComparison` and the actual upstream
   `Comparison/Defs.lean` definitions: restriction along `toProEt X`, left Kan extension
   followed by sheafification, and their canonical `comparisonAdjunction`. The module
   specialization of the former file has a finite-ring binder, so it is deliberately
   not applied here. The general upstream coefficient adjunction, also used in
   `boundedBelowComparison`, needs no such binder. Verdict: the correct comparison,
   without assuming a finite coefficient ring or choosing an arbitrary adjunction.
4. The module categories and D+: `Sheaf ... (ModuleCat.{u + 1} Λ)` is the fixed-discrete-
   coefficient encoding used by the recorded `boundedBelowComparison` and
   `proEtaleClassicalSheavesModules`. I read the latter theorem's signature and its
   constant-ring-action explanation, and `ringedSiteModules` (the transparent
   `SheafOfModules` abbreviation). This fixed-ring encoding is modules over the constant
   ring sheaf, with linear natural transformations. I read `DerivedCategory` and its
   localization Q in Mathlib Basic, `homologyFunctor` in HomologySequence, and Plus in
   TStructure: Plus is the full subcategory for `∃ n, IsGE n`, a cohomological lower
   bound. Verdict: the intended categories, rather than bounded termwise complexes or
   bounded constructible subcategories.
5. The hypothesis, for every etale D+ object, that the specified derived unit is
   invertible: `hunit : ∀ L : DerivedCategory.Plus (Sheaf ...), IsIso
   ((comparisonAdjunction ... X).derivedPlus.unit.app L)`.
   I read `Adjunction.derivedPlus` in `RightDerivedFunctor/PlusAdjunction.lean`:
   its left functor is `L.mapDerivedCategoryPlus` and right functor
   `R.rightDerivedFunctorPlus`; its unit and counit are those of the localization
   adjunction. The recorded `boundedBelowComparison` states invertibility of exactly
   this unit natural transformation. Verdict: correct unit and quantifier, retaining
   the node's conditional formulation.
6. Clause 1, inverse image lands in D+ classical: the first conjunct quantifies over
   all L in etale Plus and applies `ClassicalPlus X Λ` to the actual
   `comparisonUpperStar.mapDerivedCategoryPlus.obj L`. `ClassicalPlus` tests
   `IsClassicalComplexFor` after `DerivedCategory.Plus.ι`, and the latter tests every
   `homologyFunctor ... q`, q in Z. Verdict: all cohomology sheaves, with no fixed
   degree or fixed lower bound.
7. Clause 1, derived direct image carries all pro-etale D+ objects to etale D+:
   the right functor of the same derivedPlus adjunction is
   `(comparisonLowerStar ... X).rightDerivedFunctorPlus`, whose domain is the entire
   pro-etale Plus category and codomain is etale Plus. This follows from the existing
   canonical construction and does not depend on a classicality assumption.
   Verdict: already supplied by the typed existing functor; a tautological conjunct
   about its codomain would add no assertion.
8. Clause 2: the second conjunct quantifies over every K in pro-etale Plus, then assumes
   `ClassicalPlus X Λ K`, then asserts `IsIso (derivedPlus.counit.app K)`.
   Its source is inverse image of the actual right derived direct image and its target
   is K. Verdict: the exact counit, with hypotheses and quantifiers in the right order.
9. The final equivalence must use those two functors. The worker had only
   `Nonempty (etalePlus ≌ classicalPlus)`, which did not identify either functor.
   I repaired this to an existential equivalence e with natural isomorphisms
   `e.functor ⋙ (ClassicalPlus X Λ).ι ≅ comparisonUpperStar.mapDerivedCategoryPlus`
   and `e.inverse ≅ (ClassicalPlus X Λ).ι ⋙ comparisonLowerStar.rightDerivedFunctorPlus`.
   Thus both forward and inverse functors are the specified comparisons, through the
   full inclusion. Verdict: now exactly the source's concluding assertion, not an
   unrelated equivalence. No natural isomorphism or equivalence data are postulated
   outside the theorem's conclusion.

Dependency-module reading (H12/H13): there are no new nodes. For
`sk-def-pe-classical-definition`, I opened the recorded `ClassicalContinuityMap` module:
its `IsClassical`, `IsClassicalModule`, `IsClassicalCochainComplex` and
`IsClassicalComplex` use set sheaves or intrinsic modules over the lifted constant
ring. They do not accept the fixed-ring ModuleCat sheaves of the comparison adjunction.
The authorized interface repair reuses its actual `AffinePresentation` and
`continuityMap`, rather than recreating a site, presentation or canonical map.
`IsClassicalModuleFor` says `IsIso (continuityMap P F.obj)` for every small cofiltered
presentation; its colimit is in ModuleCat, with the restriction-induced linear map.
`IsClassicalComplexFor` applies this to every derived cohomology sheaf.
The old intrinsic predicates and the set predicate remain imported and available.
The repaired record changes only lean and explains the encoding mismatch.

The dependency node explicitly includes the cochain formulation. The worker's new
interface gave the derived formulation only, leaving the cochain formulation in the
old intrinsic encoding. I added `IsClassicalCochainComplexFor`, with actual data
`∀ q : ℤ, IsClassicalModuleFor X Λ (K.homology q)`, in the same fixed-ring encoding,
and recorded it in lean.declarations. All four new definitions are explicit predicates;
none has a sorry, choice, arbitrary map or existentially chosen object in its data.
I also replaced the two incorrect Tag 099L docstring citations with the actual
blueprint definition source: the tags table identifies 099L as the section on derived
completion over Noetherian rings, not classicality. The theorem's docstring retains
all eight proof steps and dependency names and now describes the specified functors.

Edge cases: IsCofiltered includes nonemptiness, just as the source's presentations do;
an empty index is therefore correctly excluded, while one-object diagrams and diagrams
with parallel arrows are allowed by SmallCategory. AffinePresentation carries affine
etale stages, an affine site vertex, and IsLimit after forgetting to schemes over X,
so it has the source's limit property rather than merely a site-internal limit.
The zero module's continuity map is the zero-object isomorphism; all cohomology degrees
of the zero complex are included. The empty scheme and arbitrary shifts/lower bounds
are admitted. There is no n >= 1 or characteristic restriction. Universes are explicitly
bound: Scheme.{u}, coefficient and section universe u+1, and indices Type (u+1), with
no extra universe equation, lower test universe or geometric-size assumption.

Independent searches actually run in this reading:

- LeanSearch via msearch: "For an arbitrary scheme and a discrete commutative ring the
  bounded below etale derived category is equivalent via inverse image and derived
  direct image to proetale complexes with classical cohomology". Eight hits concerned
  etale ring maps, Scheme.Etale and smallEtaleTopology; none states this result.
- LeanFinder via msearch: "essential image of exact etale proetale inverse image on
  bounded below complexes equals classical cohomology". Eight hits included acyclic
  homotopy complexes, isGE/isLE criteria and discrete condensed-set essential images;
  none was this equivalence.
- Loogle via msearch: `CategoryTheory.Adjunction, CategoryTheory.Equivalence`.
  Six hits included Adjunction.toEquivalence and Equivalence.toAdjunction. These supply
  the generic final categorical construction but do not assert the classical image.
- msearch grep: `classical.*cohomology|cohomology.*classical|ClassicalComplex|ClassicalPlus`.
  The sole Mathlib hit was ElladicCohomology.lean:34, a comparison TODO.
- Direct rg with those concepts, IsClassicalCochainComplexFor and the theorem/predicate
  names across Mathlib, upstream WeilConjectures, the side framework, lean/Sheaf and
  dag/lean_names_upstream.json found no exact existing statement or compatible fixed-
  coefficient classical predicate. I opened the plausible hits ClassicalContinuityMap,
  UnboundedSiteComparison, ProEtaleConstructibleOrigin and the framework's
  ConstructibleSheaf/ProEtaleModule/DerivedCategory. UnboundedSiteComparison assumes
  finite primary coefficients and a finite-type scheme over a finite/algebraically
  closed field; the other hits concern constructibility or intrinsic constant modules.
  None replaces this arbitrary-scheme, arbitrary-discrete-ring bounded-below theorem.

Changes made in this second reading are exactly: identify both equivalence functors,
add the missing fixed-coefficient cochain predicate, repair the two source citations,
and update the corresponding lean records. Both node copies still differ from the
repository only in lean. Their lean.statement fields are verbatim module signatures.
The DAG statement was already correct, so no statement_change or citer audit is needed.
No theorem was proved: classicalDerivedEquivalence remains the sole sorry. Lines are
at most 100 characters, all variables and universes are explicitly bound, and there
is no private declaration, file-local notation, hidden let, or local instance.

Validation after these repairs: the prescribed scompile.py invocation passed both
ClassicalDerivedDefinitions.lean and ClassicalDerivedEquivalence.lean separately,
including sandbox and library checks on the server. All completed in at most 3.2 seconds
per invocation, with no errors or warnings. No global build was run.
