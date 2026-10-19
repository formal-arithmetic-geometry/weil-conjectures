## Worker report

The delivery states `lem-pur-ordinary-adjunction-scalar-compatibility` in
`Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility`. All new theorem proofs are
`sorry`; all definitions have actual data, or extract a uniquely specified map or
an inverse equivalence. The natural statement is unchanged. No statement correction or dependency-node
repair is used. One new definition node supplies the missing normalized tensor
comparison using the existing coefficient transport; it is added to statement dependencies.

The node's clauses are represented by the following declarations (namespace
`WeilConjectures` throughout).

- The prime ell is `l : ℕ` with `[Fact l.Prime]`. The global finite-field convention
  is `D : FiniteFieldDatum`; distinct characteristics are `hl : l ≠ D.p`.
  The primary theorem and bounded restriction have `[X.Over (Spec (.of D.k))]`
  and its Y analogue, finite-type structure morphisms rendered by
  `LocallyOfFiniteType` and `QuasiCompact`, and the separated finite-type f by
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`. No `f.IsOver` is added:
  f need not preserve the separately supplied structures. The proof plan explicitly
  gives X the composite structure when applying constructible direct image.
- Finite coefficient extensions are finite-dimensional algebras over `ℚ_[l]`.
  `ι : E →ₐ[ℚ_[l]] L` renders their given inclusion. This allows each finite
  subfield of the fixed algebraic closure by specialization. For the final clause,
  `Ω : Type v` with `[IsAlgClosure ℚ_[l] Ω]`, indices
  `Padic.FiniteCoefficientFields l Ω`, and the recorded small models
  `AlgebraicallyClosedCoefficients.Coefficient.{u}` and `coefficientInclusion`
  render the actual fixed closure and nested fields.
- The small site is Mathlib `Scheme.ProEt` with `ProEt.topology`. Its object
  universe is u+1 and its morphism universe u; neither is collapsed. Coefficient
  fields have the recorded small models in u, with lifted integers in u+1.
  The closure universe v remains independent, and coefficients coming from any
  finite subextension use those canonical small models. No site-universe equality
  or extra geometric hypothesis is imposed.
- R is the published completed coefficient sheaf, used by
  `PbcCompletedDerived W (pbcIntegralDatum l E)`. Completeness is
  `ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete ...)`.
  The helper `purCoefficientIso` identifies this continuous-function presentation
  with `completedIntegralCommRingSheafUnrestricted` by forgetting to the existing
  normalized `integralDetailedCoefficientComparison`. Its finite projections
  therefore retain that existing comparison and its `integralCoefficientULift`.
  `purCoefficientModel` reuses the inverse of the landed `integralDetailedTransport`;
  `changeFunctor` expresses its forward functor as inverse ring restriction while
  retaining the landed functor as its inverse. `purCoefficientModel_predicates` identifies completeness with
  the recorded `IntegralOnSlice.IsComplete ... none` and with `IsSfDerivedComplete`,
  while the separate `purCoefficientModel_bounded_predicate` identifies bounded
  constructibility with `sfIntegralConstructible` under `[IsNoetherian W]`,
  `_hdim : ∃ n : ℕ, topologicalKrullDim W ≤ n`, and `_hinv : IsUnit (l : Γ(W, ⊤))`.
  Thus the presentation transport does not introduce a new category or predicate.
- P is exactly `pbcActualStrictCompletedPull`, the dependency's recorded functor;
  F is `pbcActualDerivedPush`, ordinary unbounded ringed direct image.
  `purStrictPullComparison` retains the dependency's unique unit-compatible
  comparison to the completion reflector.
- `purOrdinaryHom` gives h, with forward function ordinary derived adjunct after
  precomposition by `pbcActualStrictCompletedPullUnit`. Its existence proof
  `purOrdinaryHom_bijective` specifies transport from the constant-coefficient
  reflector, the constant/completed equivalence, and the right-functor comparison.
  This is defined before any constructible restriction. `purOrdinaryHom_linear`
  gives addition and O_B scalar preservation in both directions; the harmless
  ULift of O_B is the canonical ring model, not an extra coefficient ring.
- C is precisely `pbcEmbeddingAmbientTensor`, ordinary derived scalar extension
  along the canonical completed coefficient map. `purScalarComplete` uses the
  published preservation-of-completeness result. The coefficient models retain
  the actual scalar tensor maps through `purRawTensorSection`,
  `purOrdinaryScalarModel`, `purScalarModelComplexIso`, and `purScalarModel`:
  the first comparison is fixed on all pure tensor sections; the derived one is
  fixed by the universal derived tensor counit and exact restriction factors.
  The existing `sfIntegralOrdinaryComparison` is the specified chi comparison
  to strict completed integral scalar extension on bounded complete objects.
- a is `purScalarPullComparison`: C of the strict/reflector comparison, the
  inverse published `pbcScalarCompletedPullIso`, and the inverse L strict/reflector
  comparison. Its direction is C_X P_E to P_L C_Y, exactly as in the node.
  b is exactly `(pbcScalarDirectImageIso ...).hom`, without choosing a replacement.
- `purScalarRightDerivedComparison` names d. The normalization theorem compares
  its homotopy-category derived units with the ordinary identity-on-sections
  comparison, so it is the comparison of the two ringed-topos factorizations.
  `purScalarDirectImage_coefficientAdjunct` explicitly says b's coefficient
  adjunct is F_E of the coefficient unit followed by inverse d, as required by
  the node. In particular b is not silently defined only by the desired f-mate
  identity.
- The primary theorem `purOrdinaryAdjunctionScalarCompatibility` gives both
  displayed integral equations for every u and every v. Lean composes left to
  right: its forward argument is `a.inv ≫ C_X.map u`, and its target is
  `C_Y.map (h_E u) ≫ b.hom.app K`. The inverse equation has exactly the same
  source and target transports. It is an equality of actual morphisms.
- `purOrdinaryAdjunctionScalar_identity` has the multiplication-unit equations
  for a and b. `purOrdinaryAdjunctionScalar_tower` identifies both iterated
  comparisons with the direct ones through `pbcAmbientScalarComp`. These are
  the published balanced tensor maps, and their existing pentagon handles
  longer towers. `purScalarModel_coherence` identifies the model comparisons
  with ordinary tensor associators and units; conjugation by the specified chi
  comparisons and localization are exactly the definitions of
  `sfRationalScalarComp` and `sfRationalScalarUnit` used by the common-stage system.
- `purOrdinaryAdjunctionScalar_bounded` verifies membership of P_E M, F_E K,
  C_Y M, and C_X K in `sfIntegralConstructible`, when M and K have that
  membership. Its docstring records the common interval for all reductions and
  the switch to the composite k-structure in the direct-image argument.
  The same theorem instantiated over L supplies the L endpoints. The categories
  are full, so these are the actual same integral Hom groups and equations.
- `purRationalHom` is the raw tensor localization of the fixed linear Hom
  equivalence, uniquely specified on `a ⊗ₜ u`; `purRationalScalarMaps` gives the
  two actual localized scalar-extension maps, uniquely specified on every such
  tensor, including arbitrary denominators. `purLocalizedCoefficientMap`
  uses the canonical fraction-field identifications and the supplied inclusion.
  `purRationalAdjunctionScalarCompatibility` gives both equalities for every
  localized morphism, not just those coming from integral maps.
- `purRationalModelHom` identifies these tensor Hom groups with actual Hom groups
  of the recorded `sfRationalConstructibleCategory`. Its specification sends a
  pure tensor to the very same coefficient fraction and the coefficient-restricted
  integral morphism. This is raw localization with unchanged objects, not Karoubi
  completion. The coefficient-model scalar comparison is fixed on pure tensors,
  and its derived and chi comparisons identify its rational scalar maps with
  the recorded rational scalar extension.
- `purOrdinaryAdjunction_commonStage` states preservation and reflection of the
  defining equality-after-further-common-extension relation by h and its inverse.
  Each existential ranges over the actual finite subfields B of Ω containing A,
  and each transition uses the recorded `coefficientInclusion`. Given two
  representatives at different stages, the recorded common-stage construction
  first moves them to a common A; the theorem tests their equality after a further
  B in both directions. Together with the forward/inverse scalar equations and
  the identified associators, this is exactly independence of the first common
  field and of the representative. The same B witnesses either implication.

Dependency declarations read and used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties` is a convention collecting the named Mathlib scheme properties; no separate declaration is required.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteOnSlices`, `WeilConjectures.IntegralOnSlice.IsComplete`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-weil-pbc-completed-pullback`: `Sheaf.Paper.PbcActualStrictPullback`, `AlgebraicGeometry.Scheme.pbcActualStrictCompletedPull`.
- `lem-sp-completed-pullback-adjunction`: `Sheaf.Paper.CompletedPullbackAdjunction`, `CategoryTheory.ConstantCompletion.completedPullbackAdjunction`.
- `lem-weil-pbc-constant-completion-equivalence`: `Sheaf.Paper.ConstantCompletionEquivalence`, `CategoryTheory.ConstantCompletion.equivalence`.
- `lem-pur-completed-coefficient-pushforward-comparison`: `Sheaf.Paper.CompletedCoefficientPushforwardComparison`, `WeilConjectures.CompletedCoefficientPushforward.comparison`.
- `lem-weil-finite-free-completed-scalar-comparison`: `Sheaf.Paper.FiniteFreeCompletedScalarComparison`, `WeilConjectures.finiteFreeCompletedScalarComparison`.
- `prop-weil-pbc-scalar-extension`: `Sheaf.Paper.PbcScalarExtension`, `AlgebraicGeometry.Scheme.pbcCoherentScalarExtension`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`.
- `def-weil-algebraically-closed-coefficients`: `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`: `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`, `SheafOfModules.sheafRingDerivedCoefficientAdjunction`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`, `CategoryTheory.ringedToposDerivedPushforwardComposition`.
- `lem-weil-scalar-extension-composition`: `Sheaf.Paper.SfScalarExtensionComposition`, `WeilConjectures.sfRationalScalarComp`.

The new node also uses `Sheaf.Paper.BoundedConstructibleTower`
(`pbcLevelConstantComparison`, `pbcDerivedRestrict`, `pbcTensorSection`,
`pbcComplexCounit`) and the ordinary tensor interface re-exported by the recorded
`Sheaf.Paper.IntegralScalarExtensionUniverses`
(`integralOrdinaryScalar`, `integralOrdinaryDerivedScalar`).

All recorded modules of stated proof dependencies are imported without `public`.
Proof dependencies that currently have no Lean module (the generic restriction-counit
node and the collected elementary/Mathlib interfaces) are not invented or copied.
The proof docstrings retain their DAG roles for stage 3. The imported constant
completion theorem and pushforward comparison retain their complete-domain meanings.

Searches for an exact existing statement:

- msearch.py leanfinder: "completed pullback direct image adjunction Hom scalar
  extension compatibility" returned eight ordinary module pullback/adjunction
  declarations, including `PresheafOfModules.pullbackPushforwardAdjunction` and
  scheme module pullback adjunctions, none with completion, the specified a/b,
  rationalization, or common-stage conclusions.
- msearch.py loogle: `CategoryTheory.Adjunction.homEquiv, CategoryTheory.mateEquiv`
  returned zero hits. The generic mate and adjunction APIs are reused; none is
  the specialized node with its scalar normalizations.
- msearch.py grep: `homEquiv.*[Ll]inear|[Ll]inear.*homEquiv` in CategoryTheory
  returned zero hits. Direct rg of Mathlib and WeilConjectures found no new names
  and no occurrence of this blueprint id. Direct project rg found the published
  PBC comparisons and the separate constant-completion and scalar-composition
  inputs, but no statement containing all the node's Hom equations. The upstream
  ProEtale ScalarExtension module has ordinary scalar adjunctions, not this node.
- The owning presentation maps were checked against `BoundedConstructibleTower`,
  `FiniteFreeCompletedScalarComparison`, `PbcActualScalarPullback`,
  `SfScalarExtensionComposition`, and the recorded intrinsic scalar modules.
  Existing finite-level constant/continuous-function comparisons are reused.
  The repair found and reuses the landed integral stratified-perfect coefficient
  comparison and transport. The remaining helpers are its CommRing lift, section-normalized
  inverse restriction model and actual tensor comparison.
  They do not define independent mathematical notions or duplicate an existing
  recorded interface.

Edge cases checked before and during writing:

- E=L: tensor multiplication is the specified unit, not a literal equality of
  separately selected derived tensor functors; both comparison unit equations
  are stated explicitly.
- Towers and ramification: no inclusion is assumed unramified and no uniformizers
  are identified. Cofinality of their powers and the actual balanced tensor
  associator are retained in the proof plan and comparison formulas.
- Empty X or Y and zero objects: no nonemptiness or positive-dimension assumption
  appears; the complete full subcategories, quotient comparisons, and Hom tensor
  formulas still apply. Constructible preservation uses the empty-source case.
- f=id: the normalized ordinary adjunction and completion unit give the reflector
  identity on complete objects; the same scalar equations typecheck.
- Arbitrary complete complexes: no boundedness, constructibility, finite Tor
  amplitude, or resolution choice enters `purOrdinaryHom` or its linearity.
  Boundedness enters only the separately stated restriction clause.
- n=0 denotes exponent n+1=1 in all finite quotient helpers; the zero quotient
  level is not silently introduced.
- Rational morphisms are arbitrary finite sums of tensors, not integral numerators
  with an unstated denominator restriction. No faithfulness of scalar restriction
  is used. The common-stage representatives use an independent closure universe.

In the item module, compiler instance search is narrowed by disabling imported
generic instances with undetermined max-universe parameters, as in the published
PbcScalarExtension module. The existing exact restriction instances are used.
No alternative Abelian category or local notation/instance is introduced. Definitions and theorem signatures bind all
variables and universes explicitly.

## New nodes

`def-pur-completed-coefficient-presentation-transport` retains the missing normalized
ordinary/derived tensor comparison between the two published coefficient interfaces.
Its module is `Sheaf.Paper.CompletedCoefficientPresentationTransport`, with primary
declaration `WeilConjectures.purScalarModel`. Its statement explicitly REUSES
`integralCoefficientULift`, `integralDetailedCoefficientComparison`, and
`integralDetailedTransport`; it does not introduce another quotient identification.

The CommRing helper `purCoefficientIso` is uniquely characterized by the equation
`(adicLisseForget W).mapIso e = integralDetailedCoefficientComparison W l E`.
`purOrdinaryCoefficientRoundTrip` is uniquely fixed to be the identity on every
module section. `purDerivedCoefficientRoundTrip` descends this actual map through
`mapDerivedCategoryCompIso`, `mapDerivedCategoryNatIso`, and the identity comparison.
`purDetailedTransport_isEquivalence` states the equivalence property of the existing
functor. `purCoefficientModel` takes its inverse and uses `changeFunctor` with the
canonical `Iso.isoCompInverse` to express the explicit inverse restriction functor;
its inverse remains exactly the landed `integralDetailedTransport`.

`purCoefficientModel_predicates` gives only the two completeness equivalences for
arbitrary W. `purCoefficientModel_bounded_predicate` separately renders the bounded
constructible equivalence and includes all three geometric hypotheses of
`integralStratifiedPerfectDetailed`. The source of these hypotheses is
Bhatt--Scholze 6.5.1 and 6.8.11(3), as recorded in that landed node.

The new tensor-comparison clause uses the actual `pbcTensorSection` and
`purRawTensorSection` for the local pure tensor formula. Its derived normalization
is the displayed equation on every complex in `purScalarModel_existsUnique` with
the actual derived tensor counit, exact restriction factors, and termwise ordinary
comparison. Uniqueness determines every chosen datum; no definition takes a
mere unspecified Nonempty isomorphism. Every theorem proof is `sorry` and has a
source and natural-language proof in its docstring. The node contains each of
these clauses, and its lean.declarations is generated from the actual module.

Additional dependency read and reused: `lem-weil-pbc-integral-stratified-perfect-characterization`,
module `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`, declarations
`AlgebraicGeometry.Scheme.integralCoefficientULift`, `integralDetailedLevelComparison`,
`integralDetailedCoefficientComparison`, `integralDetailedCoefficientRestriction_exact`,
`integralDetailedTransport`, and `integralStratifiedPerfectDetailed`.
The new node cites this dependency. The item gains only the new definition node;
its natural statement and all other metadata are copied from the current shared base.

## Repair of returned delivery

1. H4/H12: the retained source still had the duplicate quotient theorem and definition,
despite its report. Both have been removed. The finite comparison is already supplied by the landed
`integralDetailedLevelComparison`, using `integralCoefficientULift`; the retained
`purFiniteSheafIso` helper was also removed as unnecessary. The completed CommRing lift forgets to the existing
`integralDetailedCoefficientComparison`, and the model is constructed from the inverse
of the existing `integralDetailedTransport`, as detailed above. This replaces the
independent duplicate model-equivalence construction.
2. H3: completeness is separate. Bounded constructibility is asserted only with
Noetherian W, a finite Krull-dimension witness and ell invertible on W. These hypotheses
are available on X and Y in the item's finite-field finite-type setting. There is
no claim of bounded comparison for arbitrary W in either the Lean or the new node.
3. H3 secondary: `purRationalAdjunctionScalarCompatibility` and
`purOrdinaryAdjunction_commonStage` explicitly bind D, hl, both finite-type/quasi-compact
k-structures, and the separated finite-type f, exactly like the main theorem.
The retained source also declared the rational, identity and tower theorems in
both files. They now occur once, in the owning item module. The omitted
`purOrdinaryHomLinear` definition and rational existence theorem docstring were
restored from the retained original packet. The item's main signature is unchanged.

No unit statement changes and no dependency-node repairs are needed. The new node
is a definition added in this delivery; its text was corrected as part of repairing
that new node, without changing the item's statement.

## Searches in this repair

Direct rg for `integralDetailedCoefficientComparison|integralDetailedTransport|integralCoefficientULift`
in lean/Sheaf/Paper and upstream WeilConjectures found the landed integral
stratified-perfect module. Its full signatures, normalization and docstrings were
read. Its equivalence goes from the intrinsic category to the PBC category; this
delivery uses its inverse, retaining the existing functor rather than replacing it.
The earlier report's claim that no such coefficient comparison existed was incorrect.
The earlier Mathlib search records remain as historical searches, with the corrected
project search result in the new node's mathlib_searches.

Fresh msearch.py LeanFinder query: "transport derived category along an isomorphism
of coefficient ring sheaves inverse restriction of scalars compatibility tensor".
Eight hits included `SheafOfModules.restrictScalars`, `pushforwardCongr`,
`freeFunctorCompPullbackIso`, `Functor.mapDerivedCategorySingleFunctor`, and
`PresheafOfModules.restrictScalarsCompToPresheaf`. These are generic ingredients,
not the specified normalized completed-coefficient tensor comparison. Loogle query
`CategoryTheory.Iso.isoCompInverse, CategoryTheory.Equivalence.changeFunctor`
returned no hits; direct Mathlib source inspection located both APIs and they are used.
The direct DAG search finds the integral-stratified characterization and generic
ringed presentation transport; neither supplies the pure-tensor-normalized comparison
with the intrinsic ordinary scalar interface. blueprint_refs.py search
"coefficient presentation" returned only `def-tw-frobenius-action`, which does not
state this comparison.

## Validation

All checks use scompile.py and deliver2.py only. Final results are appended after
the completed clean compile and server preflight. No global build or direct git
command is used. The maintainer performs the independent review.

Fresh Mathlib LeanSearch for "The normalized derived scalar tensor comparison under
an isomorphism of completed coefficient sheaves" returned eight sheafification,
monoidal-normalization and ordinary tensor/derivation hits, none giving this
completed scalar comparison. Mathlib grep `mapDerivedCategoryCompIso|isoCompInverse|restrictScalars`
in CategoryTheory returned five hits including `CategoryTheory.Iso.isoCompInverse`
in Equivalence.lean:738, which the definition now uses. Exact search outputs are
preserved in the new node's mathlib_searches.

## Second reading by Q55

Independent maintainer reading, 2026-10-18, of immutable delivery
`19ae07f9ed22b77db63943284a4aaa3b73e13c04`. This section records the
independent reader's work, not an additional reading attributed to the author.

The item node, all twenty statement-dependency records, both delivered modules
(263 and 620 lines), and the worker report were read. The additional dependencies
of the new presentation node were checked in the read-only Q55 clone where they
are not extracted into this packet. No project file or branch was edited.

Source places read: main-20261015 `sec-six-functors-basics/sk-lem-sf-mate/
fix-prop-adjunctions.proof.md`, Step 1; Stacks `proetale.tex` lines 4271-4388,
section-derived-completion-noetherian, lemma-naive-completion (099M), and
lemma-pushforward-Noetherian-case (099N), especially (1), (2), (5);
Bhatt--Scholze, printed pp. 58-59, Lemma 6.8.2(1). The source supplies ordinary
adjunction, completion and the coefficient presentation; scalar naturality is
correctly identified as an extracted argument rather than a verbatim theorem.
The ordinary module tensor-adjunction and derived coefficient-adjunction
normalizations were also read in their recorded Lean modules and docstrings.

Hypothesis and clause audit:

| Node datum or clause | Delivered rendering and reading |
| --- | --- |
| Distinct primes, geometric base field | `Fact l.Prime`, `FiniteFieldDatum.{u}`, `hl : l ≠ D.p`; the datum includes a finite field and its algebraic closure. |
| Finite-type schemes, separated finite-type f | Both `Over` structures and their `LocallyOfFiniteType`/`QuasiCompact` instances, and the three instances on f. No extra `IsOver f` or smoothness/properness assumption. |
| Finite coefficient inclusion | Finite-dimensional Q_l-algebras E,L and the algebra homomorphism ι. This represents inclusions after identification with their images; it introduces no ramification restriction. |
| Small site and completed coefficients | Mathlib `Scheme.ProEt`, `ProEt.topology`, `pbcIntegralDatum`, and `PbcCompletedDerived`; the coefficient-model comparison reuses `integralDetailedCoefficientComparison`. |
| Every derived-complete M,K | Full subcategories of `PbcIsIntrinsicallyComplete`, without boundedness or constructibility in the Hom equivalence. |
| P and F | Actual strict-tower pullback `pbcActualStrictCompletedPull` and actual ordinary ringed direct image `pbcActualDerivedPush`. `purStrictPullComparison` is the uniquely unit-compatible comparison, not a new pullback. |
| Specified h and inverse | `purOrdinaryHom` is `Equiv.ofBijective` of actual completion-unit precomposition followed by `pbcActualDerivedAdjunction.homEquiv`; its inverse is thereby fixed. |
| Linearity in both directions | All four addition/scalar equations in `purOrdinaryHom_linear`, then the same linear equivalence in `purOrdinaryHomLinear`. |
| C and a | `pbcEmbeddingAmbientTensor`, `purScalarComplete`, and `purScalarPullComparison`; the latter is C of the strict comparison, inverse published scalar/pullback comparison, inverse target strict comparison, in precisely the requested direction. |
| Specified b and d | b is the published `pbcScalarDirectImageIso`. d is adjunction conjugation of the normalized pullback comparison. `purScalarRightDerivedComparison_normalization` fixes the universal right-derived comparison; `purScalarDirectImage_coefficientAdjunct` gives exactly F_E of the coefficient unit followed by inverse d. |
| Forward scalar equation | `purOrdinaryAdjunctionScalarCompatibility.1` has argument `a.inv ≫ C_X.map u` and value `C_Y.map (h_E u) ≫ b.hom.app K`. |
| Inverse scalar equation | The second conjunct has the inverse L-bijection on `C_Y.map v ≫ b.hom.app K`, equal to `a.inv ≫ C_X.map (h_E.symm v)`. Quantifiers and endpoints match. |
| Identity and towers | `purOrdinaryAdjunctionScalar_identity` and `_tower` retain the actual multiplication units and `pbcAmbientScalarComp` associators, for both a and b. |
| Bounded constructible restriction | `_bounded` puts P_E M,F_E K,C_Y M,C_X K in `sfIntegralConstructible`; the coefficient-model bounded predicate has exactly Noetherian, finite-dimensional, ell-invertible hypotheses. The proof explains the composite k-structure needed for direct image. |
| Raw rational localization | `purRationalHom` and `purRationalScalarMaps` have unique formulas on every pure tensor, using the actual fraction-field inclusion. `purRationalAdjunctionScalarCompatibility` states both equations for all localized morphisms. `purRationalModelHom` identifies these groups with the recorded raw rational category. |
| Common-stage independence | The two related predicates mean agreement after a finite further extension through the specified a,b maps. `_commonStage` preserves and reflects that relation in both directions. `purScalarModel_coherence`, the chi-normalized `sfIntegralOrdinaryComparison`, and the recorded rational associators identify these transports with the common-stage transports. The recorded `GeneralAlgebraicallyClosedCoefficients.representatives` handles different first common fields. |

Dependency interfaces checked, beyond merely their names:

- `FiniteFieldDatum`, `Padic.finite_coefficientExtensionRing`, the conventional
  Mathlib scheme properties, `Scheme.ProEt`, `DerivedCategory`.
- `integralConstantToCompletionOfUniverses`, `IntegralOnSlice.IsComplete`,
  `pbcActualStrictCompletedPull` and its completion unit and unique comparison.
- `ConstantCompletion.completedPullbackAdjunction`, `equivalence`,
  `koszul_quotient_reflector`, and `completion_restriction`; these retain the
  reflector Hom map and the same completion units, on complete objects.
- `CompletedCoefficientPushforward.comparison` and its `ComparisonData` fields:
  ordinary identity-on-sections squares, derived normalization, strict diagrams,
  and completion. This is the ordinary right functor required by the item.
- `finiteFreeCompletedScalarComparison`, `pbcCoherentScalarExtension` and the
  actual `pbcScalarOrdinaryPullIso`, `pbcScalarDirectImageIso`,
  `pbcScalarCompletedPullIso`, `pbcScalarPreservesComplete` interfaces.
- `sfIntegralConstructible`, `sfRationalConstructibleCategory`,
  `generalAlgebraicallyClosedConstructibleCategory`, its `transport` and
  `representatives`, and `sfRationalScalarComp`/`sfRationalScalarUnit`.
- `sheafRingDerivedCoefficientAdjunction` fixes the unit and transpose on K-flat
  representatives; `ringedToposDerivedPushforwardComposition` fixes the comparison
  by derived units and its K-injective value. No faithfulness of restriction is
  used to test a derived equality.
- For the new node: `integralCoefficientULift`,
  `integralDetailedLevelComparison`, `integralDetailedCoefficientComparison`,
  `integralDetailedCoefficientRestriction_exact`, `integralDetailedTransport`,
  and `integralStratifiedPerfectDetailed`. The last theorem's geometric bounds
  are retained only for the bounded comparison. Ordinary scalar functors and
  their published universal comparisons are reused.

The new node is a genuine presentation/tensor helper. Its commutative-ring lift
is fixed by forgetting to the existing coefficient comparison. Its ordinary
round trip is fixed sectionwise; its derived round trip is constructed through
exact-functor localization. `purCoefficientModel` changes the explicit forward
model of the inverse of the landed transport, preserving that transport itself.
The scalar comparisons are fixed by local tensor generators and universal
counits on every complex. All choices determine the datum used downstream; there
is no arbitrary isomorphism selected solely from Nonempty and no hollow data.
The new node has the required definition-node fields, source, actual search
records, blueprint ancestry, empty proof/proof_deps and complete declaration
inventory. The four extra dependencies absent from this extracted subset exist
in the Q55 clone; their absence from the packet extraction is not a dangling DAG
citation. No statement correction or dependency repair is needed.

Proof-plan audit: Steps 1-3 verify geometric/coefficient hypotheses, the fixed
Hom map, and linearity. Steps 4-8 use finite freeness/cofinality, the explicit
coefficient unit, normalized composition and completion-unit injectivity to
identify the specified transpose. Step 9 is the displayed naturality calculation,
which is genuinely elementary. Steps 10-13 supply identity/tower coherence,
constructible restriction, tensor localization on arbitrary fractions, and
common-stage descent. These arguments remain in the ordinary derived route.
The item and helper cite no id on `origin/newtargets-dag:coord/route-pivot-dropped.txt`.
There is no route-pivot repair note at the specified path. No enhanced
localization, Quillen/coherent-section or operadic replacement is introduced.

Edge cases: zero objects and empty schemes need no exclusion; f=id and E=L use
the specified units; ramified extensions use cofinal powers, not equal
uniformizers; n=0 in the implementation denotes positive quotient exponent n+1;
unbounded complete complexes occur before bounded restriction; arbitrary rational
morphisms include all finite sums of fraction tensors. The common-stage closure
universe v is independent. `Scheme.{u}.ProEt` retains object universe u+1 and
morphism universe u, with coefficients lifted to u+1; no equality of these site
universes is imposed. The field models at finite common stages are the recorded
small `Coefficient.{u}` models. No extra Noetherian/finite-dimensional/invertible
hypothesis is silently imposed on the arbitrary-W completeness comparison.

Uniqueness searches: the worker's LeanSearch, LeanFinder, Loogle and grep records
were read, including the corrected search that found and reused the landed
stratified-perfect coefficient transport. Independent rg searches of project,
Mathlib and upstream WeilConjectures found no exact completed-adjunction scalar
statement or collision with the new declarations. Generic adjunction, tensor and
localization APIs are reused rather than redefined. Independent msearch Loogle
`CategoryTheory.Adjunction.homEquiv, CategoryTheory.mateEquiv` returned zero hits.
Independent LeanFinder query `completed adjunction Hom scalar extension compatibility`
returned eight generic ModuleCat change-of-rings declarations, including
`ModuleCat.homEquiv_extendScalarsComp` and tensor-evaluation formulas, with no
completion, ringed-topos direct image or common-stage statement. These do not
replace this node. The delivery branch ref was not present in the shared clone;
its immutable commit and parent were available for read-only comparison. No Git
mutation was performed.

Mechanical checks: both node `lean.statement` fields are verbatim signatures;
the inventories contain all 19 and 27 module declarations. The item changes only
lean and adds this helper to stmt_deps. All lines of the two modules are at most
100 characters; autoImplicit is false. All 21 theorem bodies are exactly `by
sorry`; there is no local proof or sorry inside a definition. Module/declaration
source and blueprint docstrings and proof plans are present. Definitions use
real constructions or uniquely normalized theorem witnesses. No global build,
live Lean write, delivery, merge or branch mutation was performed.

Compiler reproduction: the prescribed command was run on the two immutable
snapshot files, in dependency order:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q55 \
  lem-pur-ordinary-adjunction-scalar-compatibility \
  snapshot/lean/Sheaf/Paper/CompletedCoefficientPresentationTransport.lean \
  snapshot/lean/Sheaf/Paper/OrdinaryAdjunctionScalarCompatibility.lean
```

Exit code 0; no diagnostics. The installed wrapper runs its persistent overlay
on the server with `--wire-confirm` (not a manually invoked ssh command). Output:
private helper overlay 23.2s; preliminary helper 11.1s; sandbox helper 8.2s;
library helper 21.9s; sandbox item 20.0s; library item 73.7s as reported by the
wrapper. The wrapper announces a 60s limit after slot acquisition; the last
reported wall time does not change its successful exit status. Both per-file
sandbox and library checks passed. No recompile is necessary for this report-only
fix. No direct preflight or global build was run.

Findings and disposition: H1/H11, the delivered Second reading section was only
a disclaimer, and its Validation section promised results without recording
completed compiler evidence. This complete independent reading and reproduced
per-file evidence repair those reporting defects. No mathematical or Lean change
is required. The complete replacement report is the only fix.
