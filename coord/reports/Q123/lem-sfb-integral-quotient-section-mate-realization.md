## Worker report

The module `Sheaf.Paper.IntegralQuotientSectionMateRealization` states the complete
normalized internal/section realization of the integral quotient scalar and geometric
adjunctions. Its only theorem is
`AlgebraicGeometry.ProEtale.IntegralQuotient.SectionMateRealization.integral_quotient_section_mate_realization`,
with proof `sorry`. Its other declarations are transparent aliases of existing
constructions or proposition-valued conjunctions spelling out this node's clauses.
There is no data supplied by `sorry` and no new independent mathematical notion.

The previous attempt's refusal concerned an unchanged stage-1 split. I checked the
current live sources before writing: the item has no Lean record, no released repair
note, and only a stage-1 `reviewed` record. The live stage-2 wrapper is the applicable
delivery route. The kept sandbox had no Lean module, report, or node packet.

Hypotheses and objects, clause by clause:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- The ring of integers and its chosen uniformizer are the existing
  `IntegralQuotient.integral l E` and the coefficient-extension constructors it uses.
  `finite l E n` is the existing finite quotient of exponent `n + 1`; `n : ℕ`
  therefore covers exactly the positive exponents in the node, including exponent one.
- `Modules Λ T` is the recorded category of internal modules over
  `condensedRingObj Λ T` on `Scheme.ProEt.topology T`. The actual scalar map is
  `coefficientMap (reduction l E n) T`, reconstructed by the transparent alias
  `scalarMap l E n T`. It is not an arbitrary map or a selected finite projection.
  `reduction` is postcomposition by the actual coefficient quotient; the recorded
  integral-limit theorem identifies it with the finite limit projection.
- The section ring and module categories are exactly `ModuleRingedComparison.ring`
  and `.modules`. The site objects remain in universe `u+1`, its morphisms in `u`,
  and coefficient sections in `u+1`. The two displayed families of
  `HasDerivedCategory.{u+1}` instances select the ordinary derived localizations;
  they impose no mathematical restriction on schemes or complexes.
- The equivalence is the given `.equivalence`, localized termwise as
  `.derivedFunctor`. The geometric operations are `QuotientChange.L`, `.F`, `.adj`
  internally and the independently specified `.derivedPullback`, `.derivedPushforward`,
  `.derivedAdjunction` in section coordinates. The aliases `pull` and `push` merely
  expose the existing `.derivedPullComparison` and `.derivedPushComparison` with the
  exact internal endpoints. `compose` and `exchange` do the same for the existing
  internal compositor and ambient exchange.
- Internal scalar extension is the existing uncompleted universal functor `D`.
  A parameter `q : ∀ T, Pair l E n T` presents the independently specified section
  scalar operations: `Pair` is only the specialized existing
  `SheafOfModules.ScalarDerivedPair` type. This type fixes ordinary extension on
  objects and maps as actual sheafified scalar extension, fixes its universal derived
  pair and K-flat computation counit, and fixes the ordinary and derived adjunctions
  by their scalar-unit and chain-transpose normalizations. Quantifying over its
  presentations makes the result independent of the presentation; it does not
  assume a comparison with internal modules or introduce an arbitrary scalar functor.
- The fixed internal balancing family is parameter `b`; `hb` requires exactly
  `PullNormalized (reduction l E n) f (b f)` for every scheme morphism. The internal
  direct-image transformation is precisely the existing `rho ... f (b f)`, formed
  with the specified internal adjunctions. No replacement lambda or rho is selected.

Conclusions and normalizations, clause by clause:

- `GeometricAgreement (integral l E)` and `GeometricAgreement (finite l E n)` use
  the given natural comparison isomorphisms. Their first clause identifies all
  geometric Hom transposes. The next two clauses explicitly identify the units
  and counits. The fourth identifies every pullback compositor, not only the four
  edges of a fixed square.
- The fifth clause of `GeometricAgreement` sends each internal flat-term K-flat
  complex to a section K-flat complex with every term flat. It uses the existing
  internal `.kFlat` and `ObjectProperty.flat` predicates and the section
  `IsKFlatIndependentCoefficients` and `IsFlatOnSite` predicates; no boundedness is
  introduced.
- `e₀` is an ordinary scalar comparison and `e` the displayed natural derived
  comparison `D ⋙ E_S ≅ E_R ⋙ q.derived`. `ScalarAgreement` requires a restriction
  comparison that is the identity on every underlying section, the unchanged
  balanced-generator formula for `e₀`, and agreement of ordinary scalar Hom
  transposes. In the existing extension convention the formula is `s tensor x`
  on both sides. The recorded symmetric tensor identification converts both sides
  to the node's right-hand `x tensor s` convention; it changes neither map.
- The fourth clause of `ScalarAgreement` is the full localization square on every
  flat-term K-flat representative, using the actual `compute` map and
  `scalarPairComplexComparison`. Thus `e` is the localization of `e₀`, rather than
  a possibly twisted derived isomorphism. Its last clause identifies the fixed
  derived scalar Hom transposes; its derived restriction comparison is explicitly
  termwise localization of the ordinary restriction comparison. Hom transposes
  determine both units and counits by applying them or their inverses to identities.
- `χ` has the node's section scalar/pullback endpoints. `BalancingAgreement` defines
  its normalization independently of every internal comparison: a section
  restriction/direct-image comparison `r` is identity on each section
  `N((siteMap f).obj W)`, and the ordinary `χ₀` is its conjugate under the two
  independently specified composite section adjunctions. This is the usual balanced
  generator map: taking an adjunct of the identity on sections sends inverse images
  of the scalar and module generators to their inverse images separately. The
  displayed derived square pins `χ` to localization of this `χ₀` on flat-term
  K-flat representatives using both scalar computation counits and exact geometric
  localization factors. No internal lambda or realization map occurs in this
  definition, so it is not a definition of χ by transport.
- The next conclusion of the theorem is the commuting comparison equation for
  `b f` and `χ f` on every internal derived object `M`. This is exactly
  `E_U^S(lambda_f)=chi_f` after the specified source/target identifications.
- The final conclusion is the analogous equation for the existing internal `rho`
  and `(mateEquiv derivedAdjunction_R derivedAdjunction_S ...χ.hom).natTrans`.
  This is exactly the independent section counit-adjunct definition of pr. These
  equalities quantify over every object, hence identify the natural transformations,
  not merely an isomorphism class or the induced homology maps.
- The last clause of each `GeometricAgreement` quantifies over every
  `ChosenCartesianSquare h f' f g`. The section exchange written there is independently
  formed by `mateEquiv` from the section geometric compositor, the specified square
  equality, and the second section compositor. Its equality with `exchange Λ sq`
  uses precisely `pull` and `push` at the four corners. It is asserted separately
  for the integral and finite rings by the two main geometric conjuncts.
- All quantifiers range over the entire ordinary unbounded derived categories. There
  is no properness, completeness, constructibility, flatness of the quotient map,
  or exchange-invertibility hypothesis. No exchange/reduction rectangle is asserted.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the existing integer, uniformizer,
  and quotient constructors imported by it.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`. The size convention has no declaration; explicit universe
  parameters implement it.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, and `coefficientMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`:
  `AlgebraicGeometry.ProEtale.sfb_integral_coefficient_limit`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` and
  `sectionRingSheaf`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull` and the published upstream
  `ModuleObject.Derived.UpperLowerStar`: the two `moduleObjectDerived*` functors
  and `CondensedRing.derivedUpperStarLowerStarAdjunction`.
- `Sheaf.Paper.SectionModuleOperationsData`: `ModuleRingedComparison.ring`,
  `modules`, `equivalence`, `pullback`, `pushforward`, `adjunction`, and compositors.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: the existing
  ordinary unbounded relative derived tensor/closed-Hom structure; scalar extension
  remains the relative derived extension specified by the dependency nodes.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem.
- `Sheaf.Paper.IntegralQuotientDirectImageComparison`:
  `IntegralQuotient.integral_quotient_direct_image_comparison`; its imported
  `IntegralQuotientCoefficients` supplies `integral`, `finite`, and `reduction`, and
  `InternalDerivedScalarComparisons` supplies `D`, `L`, `F`, `adj`, `scalarAdj`,
  `PullNormalized`, `rho`, and `compute`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv` and `conjugateIsoEquiv`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.Paper.CondensedAmbientExchange`:
  `CondensedRing.condensedAmbientExchange` and `condensedAmbientPullbackComparison`.
- `Sheaf.Paper.SectionDerivedRealization`: the already recorded
  `ModuleRingedComparison.derivedFunctor`, `derivedPullback`, `derivedPushforward`,
  `derivedAdjunction`, `derivedPullComparison`, `derivedPushComparison`,
  `derivedPullbackComposition`, and `sectionLocalizationComparison`.
- `Sheaf.Algebra.Homology.ScalarInternalHomData`: the already recorded normalized
  `SheafOfModules.ScalarDerivedPair` and `scalarPairComplexComparison`.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`: `sectionScalarMap`,
  `internalScalarGenerator`, and `internal_section_scalar_adjunction`.
- `Sheaf.Paper.SectionDerivedPushpullNormalization` and
  `Sheaf.CategoryTheory.InternalSectionTensorComparison`: the two recorded
  normalization theorems, available as proof imports through the public imports.

The already landed definition nodes `def-sfb-scalar-hom-comparison-data` and
`def-pd-section-derived-realization` are added to `stmt_deps` because the signature
uses their existing presentations and comparison constructions. No definition node
is recreated and no dependency binding is replaced. The proof dependency
`lem-sfb-internal-scalar-pullback-normalization` currently has no Lean declaration;
its module cannot yet be imported. It is cited in the complete natural-language
proof and is not needed to elaborate this stage-2 statement.

Edge cases checked before stating the theorem: exponent one is n=0; the quotient map
is allowed to be nonflat; schemes can be empty; morphisms can be identities or
nonproper; inputs can be zero complexes or unbounded complexes. The normalized
restriction comparisons are identities on all sections even on empty objects. No
argument cancels an exchange or asks that it be invertible. The choice of a
normalized universal scalar presentation q does not restrict any of these cases.

Searches (all through the prescribed msearch wrapper, plus direct source searches):

- LeanFinder: `Internal module objects and section modules unbounded derived scalar
  extension geometric pullback comparison adjunction mates`. Eight hits, including
  `SheafOfModules.PullbackConstruction.adjunction` and `PresheafOfModules.pullbackComp`;
  none identify these specified unbounded comparisons and mates simultaneously.
- Loogle: `"mateEquiv", "conjugate"`. Eight formal mate/conjugate coherence results;
  these are ingredients, not this geometric and coefficient-specialized statement.
- Mathlib grep: `mateEquiv.*conjugate|conjugate.*mateEquiv` in
  `CategoryTheory/Adjunction`: five hits in `Mates.lean`, reused rather than restated.
- LeanSearch: `Internal module objects and section modules derived adjunction scalar
  extension comparison preserves geometric mates`. Eight ordinary module adjunction
  hits, none the complete normalized unbounded realization.
- Project/upstream rg: node id, `section.mate.realization`, scalar/pullback,
  `pullIso`, and internal/section scalar comparison names. The downstream module
  `IntegralQuotientExchangeComparison` has useful partial predicates, but its node
  lists this item as a proof dependency. Importing it here would close the intended
  proof-import cycle. This delivery instead uses the underlying already recorded
  canonical operations and states the complete normalization directly. No second
  construction of an existing functor, comparison, tensor, or mate is introduced.

Source checked: blueprint main-20261015 integral proof paragraph (3), and the local
Stacks source at 07A6 (unbounded adjunction), 07A7 (unit-square-counit exchange), 09T5
(derived adjunctions), and 08BJ (exact left adjoints preserve K-injectives).
No statement correction or STATEMENT-DISPUTED flag is needed.

Validation: scompile.py checked this file separately against the live published library
both as a sandbox module (43.9 seconds) and under its delivered module name
(28.1 seconds), with no errors or warnings. Each compile retained the 60-second limit.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
