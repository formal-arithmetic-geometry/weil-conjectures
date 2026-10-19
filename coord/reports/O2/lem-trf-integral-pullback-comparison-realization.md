## Worker report

This packet retains the saved strict-system and realization constructions and states
`WeilConjectures.integralPullbackComparisonRealization` in
`Sheaf.Paper.IntegralPullbackComparisonRealization`. The conclusion is existence of
one `IntegralComparisonSystem` satisfying `IntegralComparisonRealizationCoherence`.
The node's mathematical statement is unchanged. Two definition nodes give the
previously unowned helper modules their required DAG records.

Clause-by-clause rendering:

- The binders `(l : ℕ) [Fact l.Prime]`, `E`, `L`, their `Field`, `Algebra ℚ_[l]`
  and `FiniteDimensional ℚ_[l]` instances, and `ι : E →ₐ[ℚ_[l]] L` specify the
  prime and finite coefficient extension. An algebra embedding is the coordinate
  presentation of the indicated inclusion of subextensions; identity and composite
  embeddings are included. A third finite extension and embedding occur in
  `systemScalarTower` and `scalarTower`.
- Schemes are `Scheme`, maps are category morphisms, and the binders
  `[∀ x : X, Invertible (l : X.residueField x)]` express invertibility of ell
  wherever the constructible-complete comparisons are asserted. The ordinary
  quotient-system constructions themselves require no such restriction; the
  coherence fields use exactly the node's ell-invertible scheme domain.
- `X.ProEt`, `ProEt.topology X`, `coefficientSequenceModules`,
  `scalarReductionSource`, and `sfIntegralConstructibleCategory` are the recorded
  small pro-etale site, quotient system category, completed-module category, and
  bounded constructible derived-complete full category. No substitute categories
  or alternative definitions of completeness are introduced.
- Quotient level `n : ℕ` is exponent `n + 1`. The sequence ring sheaf and
  `integralScalarQuotientSheafMap` retain actual quotient maps. The sequence site
  encodes these transitions as part of each object and morphism.
- `integralComparisonSequenceDirectImage` is sectionwise direct image along
  `(𝟭 ℕ).prod (proEtaleBaseChange f)` with the actual constant coefficient ring
  map. `integralComparisonSequencePullback` is its left adjoint, and
  `integralComparisonDerivedSequencePullback` is its exact derived functor.
  The compositor is the unique mate of the sectionwise fibre-product-pasting
  map, not an arbitrary natural isomorphism. Scalar extension uses the recorded
  universal `DerivedChangeOfRingsCochainModel` of the actual quotient ring map.
- `integralComparisonConstantAdjunction` and `integralComparisonTowerCounit`
  construct epsilon in the derived category of whole strict towers.
  `integralComparisonTowerCounit_computes` states its ordinary limit-cone
  normalization on K-injective tower complexes.
  `integralComparisonReductionFactor` is the unique adjunction comparison;
  `integralComparisonReductionCounit_formula` explicitly identifies its counit
  with extension of epsilon followed by the quotient action counit.
- `IntegralComparisonRoosModel.comparison` and `.computes` compare total derived
  limit with the actual Roos construction. `integralComparisonLimitToRoos` has
  the limit tuple in the unshifted coordinate and zero in the shifted coordinate.
- `IntegralComparisonPullbackModel.realization` and
  `IntegralComparisonScalarModel.realization` identify the existing completed
  functors with total limit of the appropriate whole quotient diagram. Their
  `normalization` fields quantify over every flat-term K-flat representative,
  every simultaneous presentation `C`, its derived isomorphism `e`, and finite
  comparisons `κ` satisfying `CoefficientReductionPresentation`. Generator
  equations fix the resulting tower identifications `q`; the final equations
  identify their Roos realizations with the already recorded representative
  comparisons for completed pullback and scalar extension. Thus replacing a
  representative or simultaneous presentation does not change the construction.
- `IntegralComparisonCoefficientData.effective` and
  `IntegralComparisonScalarData.effective` assert invertibility of the
  counit-built system maps on the stated full constructible domain.
  `IntegralComparisonCoefficientData.complete` supplies the reconstruction unit.
- `integralComparisonEta`, `integralComparisonLambda`, and `integralComparisonMu`
  are the specified realization isomorphisms. Each is a composite of the
  normalized realization and a functor applied to the actual whole-system
  counit, with the generator-normalized scalar/pullback associator in mu.
- `integralComparisonComposition` is defining pullback realization followed by
  `Rlim(c)` followed by eta inverse. `integralComparisonScalar` is lambda
  followed by mu inverse. These are definitions with real data.
- `IntegralComparisonCompositionLaws` records whole-system associativity and
  both unit equations, naturality of the integral compositor, and its realized
  associativity and both unit equations. Its equality transports are the actual
  equalities of scheme morphisms. `coherence.composition` supplies these laws
  for every finite coefficient field, including E and L. Since the maps are
  dependent functions of the actual scheme morphisms, equal maps have equal
  comparisons by substitution; associativity and the two unit equations give
  the corresponding statement for every finite iteration.
- `systemScalarComposition` is the scalar/composition equation before realization.
  `integralComparisonScalarSquareLeft` and `integralComparisonScalarSquareRight`
  define its two displayed integral composites, lifted into the existing full
  constructible category. `scalarComposition` equates these exact maps.
  `naturality` records naturality of the scalar comparison on derived morphisms.
- `systemScalarSchemeUnit` and `scalarSchemeUnit` give compatibility with the
  specified identity pullback, before and after realization.
  `systemScalarIdentity` and `scalarIdentity` give identity coefficient change
  under ordinary multiplication and completeness. The scalar unit is defined
  from `scalarCompletionIso` and `integralOrdinaryDerivedScalarUnit`.
- `systemScalarTower` is the whole-system coefficient-tower equation with the
  generator-normalized ordinary tensor associator. `scalarTower` is its integral
  counterpart, using `integralComparisonScalarAssociator`. That associator is
  defined by conjugating the ordinary derived scalar associator with the
  specified completion comparisons chi, exactly as in the node.
- `rationalScalarComposition` states the displayed equation after applying
  `sfRationalConstructibleLocalization`. All other stated equations are
  equalities of maps of the same full integral categories and therefore also
  pass through this functor; functoriality transports their composites. The raw
  category is used, with no idempotent completion or perfectness restriction.
- No field assumes finite Tor amplitude of any reduction. All representatives
  use the already recorded flat-term K-flat class.

Dependency interfaces used (module / declaration):

- `Sheaf.Paper.IntegralScalarExtensionUniverses` /
  `WeilConjectures.integralScalarExtensionOfUniverses` and its representative comparison.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` /
  `WeilConjectures.IntegralOnSlice.completedTensor`, with the imported recorded
  completed pullback `integralDerivedPullback` and `integralDerivedPullbackComparison`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` /
  `WeilConjectures.CoefficientDerivedSystemCalculus`,
  `CoefficientReductionPresentation`, and the recorded sequence evaluation,
  restriction, coefficient ring sheaves and total-limit functors.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` /
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `Sheaf.Paper.IntegralFinitePullbackComposition` /
  `WeilConjectures.integralTowerGeneralPullbackComposition`; the new ordinary
  system compositor retains its same canonical inverse-image mate normalization.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients` /
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison` /
  `WeilConjectures.finiteFreeCompletedScalarComparison`, `scalarCompletionIso`,
  `integralOrdinaryDerivedScalarUnit`, and `integralOrdinaryDerivedScalarComp`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` /
  `WeilConjectures.integralConstantToCompletionOfUniverses` and the inherited
  completed coefficient sheaves and actual constant coefficient maps.
- `Sheaf.Paper.SfIntegralConstructible` /
  `WeilConjectures.sfIntegralConstructible` and `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible` /
  `WeilConjectures.integralOperations_preserve_constructible` and its recorded
  full-subcategory pullback `constructibleIntegralPullback`.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic` /
  `WeilConjectures.sfConstructibleIntegralScalarExtension`.
- `Sheaf.Paper.SfRationalizationKaroubi` /
  `WeilConjectures.sfRationalConstructibleCategory` and its canonical localization.
- K-flat resolutions use
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` /
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
  K-injectivity uses Mathlib `CochainComplex.IsKInjective`.
  Scheme morphisms and the pro-etale site use Mathlib's recorded declarations.

Edge cases checked: empty schemes impose no missing invertibility assumption;
zero complexes and zero maps are allowed by every model; level zero denotes the
first positive quotient, not a missing zeroth quotient; identity maps and
identity coefficient embeddings occur explicitly in the unit clauses; ramified
embeddings use the actual quotient maps at equal positive exponents; repeated
fields and arbitrary finite coefficient towers remain allowed. The helper
constructions retain independent site and coefficient universes; the intrinsic
constructible category uses its recorded common universe convention. No chosen
uniformizer is replaced by an unrelated coefficient system.

Searches: the saved `msearch.py` log contains LeanFinder queries for completed
pullback/scalar coherence and ringed-sequence-site inverse image, Loogle queries
`SheafOfModules.pullbackComp` and `"pullback", "tensor"`, and Mathlib grep queries
`(integral|complet|adic).*(pullback|scalar)|(pullback|scalar).*(integral|complet|adic)`
and `sequence.*(pullback|scalar)|tower.*counit`. A new LeanSearch query
`strict quotient systems inverse image scalar change derived limit counit realization`
returned general localization and scalar-restriction facts. The generic Mathlib
pullback comparisons do not specify these varying quotient systems or normalized
completion comparisons. `rg` over project and upstream Lean found no existing
`IntegralComparisonSequence`, `IntegralComparisonRoosModel`, or
`IntegralComparisonScalarModel`; DAG and `blueprint_refs.py search` checks found
no existing nodes for either new notion. Existing related system, completion and
change-of-rings notions are imported and reused. Search responses for the new
nodes are recorded verbatim in their `mathlib_searches` fields.

No statement correction or STATEMENT-DISPUTED issue is asserted.

## New nodes

`def-trf-integral-comparison-sequence-systems` owns
`Sheaf.Paper.IntegralComparisonSequenceSystems`. It defines inverse image and
scalar change on the already existing ringed quotient sequence site, together
with their canonical composition, scalar/pullback, identity and scalar-associator
maps. Sources are Stacks 03D2, 03D3, 06YY, 0D6D and 0941 in the extracted
common-stage construction. It reuses the existing sequence site and universal
derived change of rings rather than making another system category. The searches
above find no existing normalized comparisons on this particular sequence site.
Its named postponed theorems establish continuity, ring-map naturality, the
inverse-image adjunction and exactness, and unique generator-normalized
comparison maps; each has its construction and proof plan in its docstring.

`def-trf-integral-comparison-realization-models` owns
`Sheaf.Paper.IntegralComparisonRealizationModels`. It defines the derived
whole-tower counit, Roos model and all-representatives normalized pullback and
scalar realization interfaces. Sources are Stacks 099N(2),(5), 06YY and 0941,
and the same common-stage construction. The existing coefficient calculus
supplies reduction and limit but not these pullback/scalar normalization
interfaces. Searches found no exact existing declaration. Named postponed
lemmas identify the K-injective counit, assert the whole-system coefficient
adjunction, identify its composite counit, and establish the unique normalized
limit-to-Roos map and the underlying section identification. Every definition
uses explicit categorical composites, uniquely characterized choices, or casts
through these named equality lemmas; none has sorry data.

## Second reading by N2

This is a self-check of the retained and repaired packet; the maintainer performs
the independent review. The saved packet failed ownership preflight because its
two helper modules had no node files. It also claimed more coherence than its
single `systemCompositionAssociative` field stated. I retained the underlying
751 lines of helper constructions, supplied their two definition-node records,
and replaced that incomplete proposition with the explicit laws listed above.
The report no longer claims that the main theorem is the only postponed proof:
all helper proof obligations are named and carry their owning blueprint tag.
The existing node's statement, proof, source and proof dependencies are unchanged.
A public specialization of `essentiallySmallSelf` resolves the sequence-site
instance in its inherited object universe; ordinary scalar-model projections
otherwise leave the coefficient maximum underdetermined. The general helper
APIs still have separate site and coefficient universes.
The new nodes and their Lean declarations were checked against their actual
module contents, and the theorem's binder and clause mapping was reread against
the full original node. No source-based weakening or extra hypothesis was used.

## Validation

The prescribed dry run compiled all three modules without errors or unexpected
warnings, including their imported module forms. Its first server preflight
then reported only three `lean.statement` delimiter mismatches. The records
were corrected to the exact signature text preceding `:=` or `where`. The
final dry run and delivery repeat the required compilation and preflight.

The first push attempt repeated the compilation and hit the 60-second limit in
`IntegralComparisonRealizationModels` locally and on server confirmation. Its
two long representative-normalization fields were factored, without changing
their formulas, into `IsIntegralComparisonPullbackNormalized` and
`IsIntegralComparisonScalarNormalized` in that same module. The structures now
refer to those predicates. This keeps their generated projections small; no
module was split and no compilation limit was changed.

After that refactoring, `scompile.py` passed every delivered file without
unexpected warnings. Imported-module times were 10.6 seconds for sequence
systems, 15.7 seconds for realization models, and 29.4 seconds for the main
theorem, all within the unchanged 60-second limit. The realization-model
time decreased from the earlier approximately 42 seconds.
