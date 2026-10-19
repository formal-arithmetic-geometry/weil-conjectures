## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived` as
`AlgebraicGeometry.ProEtale.siteComparison_boundedBelow`. Its proof is `sorry`.
The node's natural-language statement, statement dependencies, proof and proof
dependencies are unchanged. No new nodes and no statement correction are needed.
All writes are in this item's isolated sandbox; compilation uses only `scompile.py`.

Hypotheses and clauses, checked against the node:

- A scheme T: `(T : Scheme.{u})`, with no Noetherian, quasi-compact, affine,
  separated, nonempty, or characteristic hypothesis.
- A finite discrete ring Λ: `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]`. `Ring` does not impose
  commutativity. The coefficient and module universe is the larger universe
  already fixed by the recorded site and coefficient interfaces; site object
  and morphism universes are not equated.
- Left module sheaves and exactly the prescribed coefficient categories:
  `finiteCoefficientComparison T Λ` is the dependency's existing comparison
  into `FiniteCoefficientModules T Λ`, modules over its actual sheafified
  connected-component continuous-function ring. Its source is the dependency's
  fixed-ring presentation of etale module sheaves, canonically equivalent to
  modules over `finiteCoefficientEtaleRingSheaf`. The dependency's explicit
  etale realization and its equivalence theorem are retained unchanged.
- The comparison morphism and its inverse image: the existing
  `finiteCoefficientComparison` is `comparisonUpperStar` followed by the
  canonical `finiteCoefficientRealization`. Its adjunction is formed from the
  recorded `T.proEtaleSiteComparisonModules Λ` and the canonical coefficient
  realization equivalence. It is not an assumed adjunction or an arbitrary map.
- Bounded below derived categories and the same exact termwise inverse image:
  `(finiteCoefficientComparison T Λ).mapDerivedCategoryPlus` uses the generic
  restriction of `mapDerivedCategory` to `DerivedCategory.Plus`, which is
  the strictly full subcategory of cohomologically bounded below objects.
  The target is definitionally the dependency's
  `FiniteCoefficientDerivedCategoryPlus T Λ`; the source is the corresponding
  full bounded below subcategory of `FiniteCoefficientEtaleDerivedCategory T Λ`.
  Thus this is the dependency's `finiteCoefficientDerivedComparison` on D+.
- Full faithfulness: the first conjunct is
  `Nonempty (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.FullyFaithful`.
  `FullyFaithful` is a data type containing an inverse on the Hom maps; `Nonempty`
  makes the assertion a proposition, equivalent to bijectivity on every Hom set.
  This refers to the actual canonical functor, not some functor with the same endpoints.
- The bounded below right derived direct image: `finiteCoefficientDirectImage`
  is the inverse of the canonical realization followed by restriction
  `comparisonLowerStar`; its right derived functor is the existing
  `Functor.rightDerivedFunctorPlus` (the left Kan extension along localization,
  calculated on bounded below injective resolutions). Enough injectives is
  transported from fixed-ring module sheaves along the canonical equivalence,
  using `EnoughInjectives.of_equivalence`, without an extra hypothesis.
- The unit is a natural isomorphism: the second conjunct is
  `IsIso (finiteCoefficientDerivedComparisonAdjunction T Λ).unit`.
  The named adjunction is the actual `Adjunction.derivedPlus` of the specified
  module adjunction; the natural transformation is therefore exactly
  `id ⟶ (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus ⋙
  (finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlus`.
  It is not an existential unrelated natural isomorphism.
- No constructibility or finiteness of individual module sheaves: neither
  conjunct restricts objects beyond membership in `DerivedCategory.Plus`.
  The only `Finite` instance is on the coefficient ring Λ.

The theorem docstring records all six proof steps of the DAG node: exact
termwise comparison; good truncation and bounded below injective resolutions;
derived adjunction and representative unit identification; acyclic comparison
on inverse images of injectives; invertibility of the actual derived unit;
and bijectivity of the actual functor's Hom maps by the adjunction and unit.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, whose full signature
  is `comparisonUpperStar (ModuleCat.{u+1} Λ) T ⊣
  comparisonLowerStar (ModuleCat.{u+1} Λ) T`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, its derived and Plus categories,
  `finiteCoefficientRealization`, its additivity and finite-limit/colimit
  instances, `finiteCoefficientComparison`, its exactness instances,
  `finiteCoefficientModules_hasDerivedCategory`, and
  `finiteCoefficientDerivedComparison`, all in `AlgebraicGeometry.ProEtale`.
  The §1(B) extension `ProEtaleFiniteModuleEquivalence` imports the current
  recorded `ProEtaleFiniteModuleIntrinsicComparison` and supplies only the missing
  arbitrary-ring realization equivalence and its instance, described below.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `CategoryTheory.Adjunction.derivedPlus`, whose signature constructs precisely
  `L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus` from additive adjoints
  with L exact and target having enough injectives.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`, the restriction of the existing
  exact functor on localizations; this also implements the recorded
  `lem-weil-pbc-exact-functor-bounded-below` interface.
- Mathlib `Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `CategoryTheory.Functor.rightDerivedFunctorPlus`, the mathlib match of
  `lem-weil-pbc-right-derived-plus-injective`, with its canonical unit and
  right-derived universal-property instance (no missing project record).
- Mathlib `CategoryTheory.Preadditive.Injective.Basic`:
  `EnoughInjectives.of_equivalence`; Mathlib equivalence and adjunction APIs:
  `Functor.inv`, `Functor.asEquivalence`, `Equivalence.toAdjunction`,
  `Adjunction.comp`, `Adjunction.right_adjoint_additive`.
- The stated proof dependency modules are imported without `public`:
  `ProEtaleSiteComparisonFiniteLevel`, `BoundedBelowInjectiveResolution`,
  `RightDerivedFunctor.Comp`, `RightDerived.LongExactSequence`, and
  `RightDerived.Acyclic`. Their transitive imports also supply the recorded
  termwise homotopy adjunction, K-injective Hom-localization and generic
  ringed-site module interfaces. Mathlib matches are used directly.

Edge cases checked before writing:

- The empty scheme is allowed; no chosen point or nonempty cover is required.
- The zero ring is allowed by `Ring` and `Finite`; no nontriviality is assumed.
- A noncommutative finite ring, such as matrices over a finite field, is allowed:
  no symmetric monoidal structure on `ModuleCat Λ` or commutativity is required.
- Disconnected schemes are allowed. The coefficient presheaf remains the
  continuous-function ring on the quotient space of connected components.
- Zero complexes, arbitrary shifts, arbitrary lower bounds, unbounded above
  complexes and infinite module sheaves are allowed. Membership in Plus is a
  cohomological lower bound, not termwise boundedness imposed on every representative.
- All characteristic cases are allowed; no torsion-prime invertibility is imposed.

Searches (the prescribed search wrapper recorded them under this item):

1. LeanFinder: `The inverse image from etale to proetale sheaves of modules is
   fully faithful on bounded below derived categories`. Eight results, including
   `Scheme.Etale.forgetFullyFaithful`, full localization/single functors,
   condensed locally constant functors and fully faithful sheaf composition.
   None state this derived geometric comparison.
2. Loogle: `CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit`.
   One exact result: the generic full-faithfulness consequence of an invertible
   adjunction unit, not the geometric invertibility assertion itself.
3. LeanSearch: `etale proetale comparison derived unit isomorphism bounded below
   modules`. Service unavailable: Internal Server Error. No mathematical verdict
   is inferred from this unavailable search.
4. Mathlib grep (both wrapper and direct rg):
   `pro.?etale.*(comparison|fully.?faithful)|comparison.*pro.?etale`.
   Zero hits.
5. Source rg: the node id and the proposed declaration names had zero hits.
   The broader comparison/derived search found
   `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`.
   Its complete declaration signatures and docstrings were read:
   `isIso_derivedComparisonAdjunction_unit_app` and
   `bijective_comparisonUpperStar_mapDerivedCategory_map` lie under
   `[MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
   [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]`.
   They cannot specialize to left modules over arbitrary noncommutative finite
   rings. Its `derivedComparisonAdjunctionPlus` has those same extra assumptions.
   The generic `Adjunction.derivedPlus` has no such assumptions and is reused.
6. Project rg found the exact finite-coefficient realization and comparison in
   the recorded dependency module, but no realization IsEquivalence interface
   and no declaration of this bounded below comparison theorem. The canonical
   objects are reused rather than defined for a second time.
7. The prescribed `scompile.py --source` check for
   `WeilConjectures.SixFunctors.ProEtale.Comparison.Derived` reported no such
   module. The source search then located the actual existing module at
   `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`, analyzed in (5).

No STATEMENT-DISPUTED issue was found. The distinct arbitrary-ring equivalence
interface supplements the published constructions. No natural-language node
statement is changed.


## Dependency modules

`def-weil-pbc-proetale-modules` receives the extension module
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleEquivalence`. The current dependency
record points to `ProEtaleFiniteModuleIntrinsicComparison`; that module is
publicly imported, so its canonical intrinsic constant-ring comparison and all
original continuous-function coefficient constructions remain available. The
existing `finiteCoefficientRealization` has only an exactness interface for
arbitrary rings. The equivalence exported in
`ProEtaleFiniteCoefficientDirectImage` assumes `CommRing`, and the intrinsic
realization equivalence is for another coefficient presentation. Neither gives
the required equivalence for the particular continuous-function realization
with arbitrary finite noncommutative coefficients.

The extension states
`AlgebraicGeometry.ProEtale.finiteCoefficientRealization_isEquivalence_ring`
with proof `sorry`, and defines the named instance
`finiteCoefficientRealizationIsEquivalenceRing` by referring to it. Its proof
docstring explains the unique local extension of fixed scalar actions along
`finiteCoefficientScalarMap`, gluing of actions and linear maps, and the unit
and counit. This is the canonical realization already constructed in the
published module; it introduces no new module category or coefficient map.
`Functor.inv` is the standard inverse of this specified equivalence, determined
up to the natural isomorphism used downstream. No definition selects arbitrary
data from a mere existence theorem.

The dependency node is copied afresh from the current shared repository and
changed only in `lean`; in particular its newer `reviewed_lean` metadata and
all statement/proof fields are retained. Its `lean.note` explains the unusable
interface and the extension. There are no new nodes or statement corrections.

## Repair of return L, immutable head ee9da21a1e10

The return reported file-only compilation failure at preliminary
`ProEtaleFiniteModules`, followed by the first sandbox check, but supplied no
Lean diagnostic. A fresh two-file compilation of that old delivery completed
successfully here, so the exact earlier failure was not reproduced.

The delivery has nevertheless been repaired substantively: it no longer
replaces and recompiles the full published `ProEtaleFiniteModules` module to
append two declarations. Those two declarations now live in the small
`ProEtaleFiniteModuleEquivalence` extension, importing the dependency's current
recorded module. The item's public import uses that extension. This avoids
redeclaration/replacement of the published coefficient constructions and
preserves the more recent intrinsic-comparison interface from the current
record. Both files explicitly enforce `set_option autoImplicit false`.
The theorem's signature and all mathematical definitions and hypotheses are
unchanged.

New searches during the repair:

- LeanFinder, `canonical sheafification realization equivalence sheaves of modules
  constant ring locally bijective scalar map`: eight hits, including
  `PresheafOfModules.sheafificationHomEquiv`, `sheafifyHomEquiv`, and the
  sheafification adjunction formulas. Reading their full source shows that they
  construct the general associated-module-sheaf adjunction, not this specific
  realization equivalence on fixed-ring sheaves. The published realization
  already uses that Mathlib construction.
- Loogle, `CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit`: the generic
  full-faithfulness consequence, which does not establish the geometric unit.
- Mathlib grep, `pro.?etale.*(comparison|fully.?faithful)|comparison.*pro.?etale`:
  no hits.
- Direct `rg` of project and upstream sources found no existing
  `finiteCoefficientRealization_isEquivalence_ring` or
  `finiteCoefficientRealizationIsEquivalenceRing`, nor the item's theorem.
  The existing commutative-ring equivalence and the different intrinsic
  coefficient realization were opened and checked in full.
- `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` confirmed
  the current published definitions and exactness interface. The current
  `ProEtaleFiniteModuleIntrinsicComparison` and `ProEtaleSiteComparison`
  declarations were also read. The local Stacks source was reread at
  `section-comparison`, `lemma-relative-comparison` (099V), and
  `lemma-compare-derived`; the last explicitly permits an arbitrary ring.

## Validation

`scompile.py Q15 thm-weil-pbc-site-comparison` compiled both delivery files
separately in dependency order, including preliminary, sandbox and library
checks. All passed with exit status 0 and no errors or warnings. The extension's
preliminary check took 4.1 seconds, sandbox 3.1 seconds, library 3.2 seconds;
the item's sandbox and library checks took 3.2 and 3.4 seconds. The default
60-second limit was unchanged. No global build or live-file edit was performed.
Both JSON `lean.statement` fields are the corresponding file signatures verbatim.
The required `deliver2.py --no-push` is run after this report update; the fresh
second reader will record its own review and deliver.


## Second reading by Q15

Independent second reader, 2026-10-16. I read the item node and both original
sandbox modules, the coefficient dependency node and its recorded module, the
comparison-morphism node and its module, and the relevant dependency signatures.
The final delivery has one module and one node: the equivalence extension and its
dependency-node override have been removed, as explained below. The earlier
Worker report and repair history are retained above; this section records the
final reviewed assembly and supersedes their claim that an extension is needed.

Source check first: the saved Stacks `scratchpad/proetale.tex`,
`section-comparison` (lines 3737 onward), assumes only that X is a scheme, with
compatible choices of the two sites. `lemma-relative-comparison` (099V, lines
3952 onward) states that the actual unit K -> R epsilon_* epsilon^{-1} K is an
isomorphism for every bounded below complex, and computes it using bounded below
injectives and Leray acyclicity. `lemma-compare-derived` (lines 4067 onward)
explicitly permits an arbitrary ring Lambda and gives the corresponding fully
faithful derived inverse image. Thus the node's restriction to finite discrete
rings has no implicit commutativity, nonemptiness, characteristic, Noetherian,
quasi-compactness, or constructibility hypothesis. No statement correction is
needed and there is no statement_change or citer audit to validate.

Item-by-item inventory of the natural statement and its Lean rendering:

1. Object T, an arbitrary scheme: `(T : Scheme.{u})`. Verdict: exact; no
   geometric property instances occur.
2. Object Lambda, a finite discrete ring with left modules:
   `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ] [TopologicalSpace Λ]
   [DiscreteTopology Λ]`. Verdict: exact. Ring is not CommRing or a field,
   and ModuleCat uses left scalar actions. Discreteness is specified rather
   than silently omitted.
3. Small sites and coefficient categories of def-weil-pbc-proetale-modules:
   the source of `finiteCoefficientComparison T Λ` is
   `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`; its target is
   `FiniteCoefficientModules T Λ`. I opened `ProEtaleFiniteModules` and
   `RingedSiteModules`: the latter target is exactly SheafOfModules over
   `finiteCoefficientRingSheaf`, obtained by sheafifying continuous functions
   on `ConnectedComponents U.left` with quotient topology and restriction by
   precomposition. On the etale side, `finiteCoefficientEtaleRealization`
   and its arbitrary-ring IsEquivalence statement identify this fixed-ring
   encoding with modules over `finiteCoefficientEtaleRingSheaf`, the
   sheafified constant ring. Verdict: the specified coefficient categories,
   through their recorded canonical presentation, not a private replacement.
4. The comparison morphism and its inverse image:
   `finiteCoefficientComparison` is definitionally `comparisonUpperStar`
   followed by `finiteCoefficientRealization`. The recorded
   `Scheme.proEtaleSiteComparisonModules` is precisely
   `comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⊣
   comparisonLowerStar (ModuleCat.{u + 1} Λ) T` and uses the existing
   inclusion Scheme.toProEt and the constructed sheaf adjunction.
   Verdict: the actual comparison inverse image, with its scalar realization.
5. Its functor on bounded below derived categories:
   `(finiteCoefficientComparison T Λ).mapDerivedCategoryPlus`.
   I read the generic ExactFunctor declaration: it restricts the exact
   termwise mapDerivedCategory to the cohomologically bounded below full
   subcategories, using preservation of homology and of IsGE. The target is
   the recorded FiniteCoefficientDerivedCategoryPlus with the same standard
   localization instance. Verdict: exactly D+ -> D+, with no termwise bound
   on every representative and no upper bound.
6. Full faithfulness of that specified functor:
   `Nonempty (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.FullyFaithful`.
   FullyFaithful contains the inverse of its Hom maps and Nonempty expresses
   existence as a proposition. Verdict: bijectivity on every Hom set of the
   actual functor; no replacement functor or restricted class of complexes.
7. Right derived direct image and its adjunction:
   `finiteCoefficientDirectImage` is the inverse of the canonical coefficient
   realization followed by comparisonLowerStar. The module adjunction is
   the composite of the recorded comparison adjunction with
   `finiteCoefficientRealization.asEquivalence.toAdjunction`.
   `finiteCoefficientModulesEnoughInjectives` transports enough injectives
   through this equivalence; none are assumed as a new hypothesis.
   The named derived adjunction is exactly `Adjunction.derivedPlus`, whose
   signature I read: its right adjoint is `rightDerivedFunctorPlus`, the
   Mathlib right derived functor formed along the bounded below localization.
   I also read `derivedPlus_unit_app_fac`, which identifies this unit with
   the ordinary unit followed by the right-derived comparison on complexes.
   Verdict: the right derived direct image and adjunction specified by the
   node, canonically transported through coefficient realization.
8. The actual unit is a natural isomorphism:
   `IsIso (finiteCoefficientDerivedComparisonAdjunction T Λ).unit`.
   Its type is id -> mapDerivedCategoryPlus followed by rightDerivedFunctorPlus.
   Verdict: the specified natural transformation is invertible, not merely
   an unrelated natural isomorphism between the same functors.
9. No finiteness or constructibility of individual module sheaves:
   there are no such hypotheses or subcategories in either conjunct.
   Verdict: all D+ objects are included; only the coefficient ring is finite.

Edge cases: the empty scheme, empty covers used in coefficient sheafification,
zero ring, zero sheaves and complexes, disconnected schemes, noncommutative
finite rings, every characteristic, degree zero and negative degrees, arbitrary
lower bounds, arbitrary shifts, and unbounded-above complexes are all allowed.
There is no externally quantified index set to constrain. Site objects retain
universe u+1 and site morphisms universe u; coefficients and module sections
are in u+1, as fixed by the dependency. No extra equality of site universes,
smallness condition, or independently smaller test-object universe is imposed.
Both files originally bound u and enforced autoImplicit false; the remaining
file still does. Thus no unbound variable or universe is hidden by elaboration.

Independent searches (recorded by msearch under this item):

- LeanFinder: `bounded below derived etale proetale inverse image unit fully
  faithful arbitrary ring`. Eight hits, including Etale.forgetFullyFaithful
  and standard-etale algebra equivalences; none is this derived comparison.
- Loogle: `PresheafOfModules.sheafification`. I opened Mathlib's returned
  sheafificationAdjunction, sheafificationHomEquiv, and counit-isomorphism
  interface in Algebra/Category/ModuleCat/Presheaf/Sheafification. They give
  the general module sheafification adjunction, not the present comparison
  theorem. The construction is already used by the recorded realization.
- LeanSearch: `inverse image etale proetale bounded below derived modules
  natural unit isomorphism`. Service returned Internal Server Error and was
  recorded unavailable; no mathematical conclusion is drawn from it.
- Wrapper grep: `constant.*module.*equiv|module.*sheafification.*equiv|
  siteComparison_boundedBelow`. Three generic equivalence hits, no item match.
- Direct rg of Mathlib's sites and algebraic geometry, project lean/Sheaf,
  and upstream WeilConjectures used comparison/unit/full-faithfulness and
  realization/equivalence vocabulary. I opened the upstream
  SixFunctors/ProEtale/Derived/Comparison declarations, including the
  surrounding section variables. Its derivedComparisonAdjunctionPlus,
  isIso_derivedComparisonAdjunction_unit_app, and
  bijective_comparisonUpperStar_mapDerivedCategory_map require a symmetric
  closed monoidal coefficient category and functorial flat resolutions.
  They do not give this arbitrary-noncommutative-ring statement. The generic
  derivedPlus construction is reused. The nearby LowerStarAcyclic declaration
  concerns global-sections cohomology and does not state this theorem either.

Mismatch found and repair:

The first fresh two-file scompile failed with two already-declared errors for
finiteCoefficientRealization_isEquivalence_ring and
finiteCoefficientRealizationIsEquivalenceRing. Both local diagnostics and
server confirmation agreed. The read-only local shared source was stale here.
I used the authorized `scompile.py --source` for ProEtaleFiniteModules and
ProEtaleFiniteModuleIntrinsicComparison and read their full current sources.
The current published ProEtaleFiniteModules already contains exactly the
arbitrary-Ring theorem and its named instance, with precisely the same
signature and canonical finiteCoefficientRealization as the extension.
The recorded intrinsic-comparison module publicly imports that source.
Therefore the proposed dependency extension is now a duplicate (H4), although
its mathematical content matches the dependency node. I removed its sandbox
module and dependency-node override, and changed the item's sole public
coefficient import to the dependency's recorded
Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison. This reuses
both published declarations without weakening any assumption or changing any
canonical construction. No dependency record is overwritten, and no new node
is delivered. All other mathematical declarations and the item signature are
unchanged. The existing source's noncommutative equivalence also avoids any
need to specialize the CommRing-only ProEtaleFiniteCoefficientDirectImage API.

The surviving helpers contain explicit constructions, transported instances,
and the canonical inverse of a specified equivalence. They do not select an
arbitrary functor or choose from a mere Nonempty existence assertion. The only
postponed proof in the delivery is siteComparison_boundedBelow, with the
matching item node and a docstring giving all six DAG proof steps. Every
remaining declaration has a source/blueprint docstring; no theorem is proved,
no private copy or file-local notation is introduced, and all lines are within
100 characters. Both original signatures were mechanically checked verbatim;
the final item signature remains unchanged and verbatim equal to lean.statement.
All non-lean fields of the item node are unchanged from the shared repository.

Second-reader validation: after removing the duplicated extension, scompile.py
compiled the only delivered file separately in its sandbox and library contexts,
exit status 0, no errors or warnings (7.6 s and 5.8 s respectively), under the
unchanged 60-second limit. No live source, global build, or direct git command
was used. The required delivery dry run follows this report update.
