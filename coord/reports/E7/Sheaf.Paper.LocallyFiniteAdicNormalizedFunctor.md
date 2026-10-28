## What changed

Implemented `WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_exists` with
its statement unchanged. The proof constructs `StageSystem.descFunctor`, proves
additivity on common-stage representatives, builds the shift commutation for the
published native pair shift, and proves its restriction isomorphisms commute with
shifts. Finite-stage representation of distinguished triangles proves triangulatedness.
The finite integral comparison components give the global comparisons; their
naturality follows from the stage restriction formula.
Evaluating the actual `isoToStage` arrow gives the inverse cocone leg, so the finite
completion-map equation gives the literal required `common_field` equation.

Added three modules: `LocallyFiniteAdicCoefficientPresentations`,
`LocallyFiniteAdicCoefficientSystem`, and `LocallyFiniteAdicFiniteCocone`. The middle
module proves commutativity of the existing native coefficient by its proved monoid
isomorphism with the other coefficient model, and proves exactness and additivity of
`sections` from the proved scalar-forgetting and section-module equivalences. It
packages these proved properties with the remaining coefficient-presentation assertion.
The two remaining obligations are coefficient comparisons and finite-field tensor
realization; neither asserts any functor on the common-stage quotient.

The finite normalization proposition is a concrete irreducible definition. Profiling
showed that repeating its expanded type in generated structure declarations cost most
of a 68-second compile; naming the proposition reduced the file to 20 seconds. No shared
definition or attribute was changed. See
`coord/changes/E7-native-finite-cocone-descent.md` for all new interfaces.

All four delivery modules compiled through `lcompile.py`, in import order, within the
60-second file limit. The final assigned-module compile took 29.0 seconds against the
current private overlay. Profiling options were removed before this check.

## Proved and sorry left

Closed the original whole-proof hole in
`WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_exists` by a complete
Lean combination of two strictly smaller assertions. This is a decomposition, not a
net proof: one original hole is removed and two new holes are added (net minus one).
The assigned module has zero remaining direct holes.

Additionally proved
`WeilConjectures.LocallyFiniteAdicRealization.coefficientSystem_exists`; the native
commutativity, section equivalence, additivity and exactness in this proof use only
proved existing results. Its normalized coefficient family uses the first hole below.

Every remaining direct `sorry` in this delivery is exactly the whole proof of one of:

- `WeilConjectures.LocallyFiniteAdicRealization.coefficientPresentations_exists`
  (`lem-sf-locally-finite-adic-coefficient-presentations`): only the inverse-limit,
  localization and pointwise finite-field coefficient maps and their scalar equation.
- `WeilConjectures.LocallyFiniteAdicRealization.finiteCocone_exists`
  (`lem-sf-locally-finite-adic-finite-cocone`): only the finite-field tensor realizations
  and their normalized scalar comparisons. This has no global pair functor, no
  common-stage Hom descent, and no global triangulated or integral comparison claim.

No holes occur in definitions, private helpers or partial proofs. Empty schemes,
identity field extensions, non-quasi-compact site objects and ramified extensions
were checked against the formulations: no nonempty-object, global-boundedness or
unramified assumption was introduced. The finite coefficient maps are locally defined
functions, not a claim that arbitrary continuous rational functions are globally bounded.

## No longer needed

Removed these nine direct proof imports from the assigned module:

- `Sheaf.Paper.ContinuousRationalDerivedRealization`
- `Sheaf.Paper.RationalRealizationScalarCoherence`
- `Sheaf.Paper.RationalCoefficientCategoryComparison`
- `Sheaf.Paper.ContinuousCoefficientRealizations`
- `Sheaf.Paper.CondensedQbarFunctionCoefficients`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.CondensedFlatCoefficientCalculus`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`

The finite realization and scalar-coherence nodes are retained in the finite-cocone
node's plan, where they belong. That plan uses the datum-free
`lem-fd-integral-identity-rational-equivalence` in place of the old global-finite-datum
`lem-fd-rational-coefficient-category-comparison` dependency.

The new coefficient route uses the existing native ring isomorphism and direct
continuous completion/localization APIs. It does not directly need
`lem-weil-pbc-condensed-qbar-function-coefficients`,
`lem-weil-pbc-condensed-flat-coefficient-calculus`,
`lem-weil-pbc-exact-functor-derived-factorization`, or
`lem-weil-sheaf-scalar-extension-ring-iso`. These were removed from this item's direct
proof dependencies. The derived-complete, finite-Tor and rational-stage definitions
remain needed by the imported statements. No source-library declaration or module was
withdrawn, and no claim is made that these modules are absent from every other target's
closure. `SfFrameworkCommonStageDescent` remains a proof import for its already proved
generic pair-shift and transition-map lemmas; its specialized framework theorem is not
assumed to produce the native realization.

## Where the brief, the DAG or earlier work was wrong

No false statement or assigned repair was found. The queue entry was an ordinary
one-hole proof item, not a zero-hole rework. Existing normalized-functor data and its
public imports were kept verbatim. The unit's `realized` record is empty, and this
construction preserves its native realization route.

The previous plan described a characteristic-free native functor but listed the
finite-field-datum comparison as a direct dependency. The newer datum-free integral
identity comparison provides the appropriate finite-stage route instead. The global
pair shift is a normalized chosen shift, so the canonical `StageSystem.Exact` shift
instance cannot simply replace it. The proof uses the already proved generic shift
transport formulas with the actual chosen source shift.

A read-only dependency audit also found the pre-existing two-node cycle
`lem-pc-ring-hom-extension-differential` to
`lem-pc-ring-hom-extension-differential-adjacent` and back. Neither node is changed
here, and none of the new nodes participates in that cycle.

The item has no imported blueprint ancestor (`blueprint_refs.py ancestor` reports
`None`). Searches for continuous coefficients and realization in the current blueprint
were recorded; the new nodes retain the item's native-realization provenance and
Bhatt--Scholze citations, rather than inventing a blueprint statement.

## New nodes

`lem-sf-locally-finite-adic-coefficient-presentations` states only normalized coefficient
presentations and their scalar equation, over any scheme. It cites the existing
continuous completion and localization results and includes pointwise proof details.

`lem-sf-locally-finite-adic-coefficient-system` packages those presentations with the
proved native commutativity and exact additive section transport. Its attached theorem
is proved, and the data structure is explicit.

`lem-sf-locally-finite-adic-finite-cocone` isolates the finite tensor functors, their
coherent scalar isomorphisms, shift compatibility and completion normalization. The
assigned module contains the full descent from these finite data to its unchanged
global conclusion. Its large normalization predicate is explicit and has no holes.

Change record: `coord/changes/E7-native-finite-cocone-descent.md`.

## Related modules compiled before delivery

13 related module(s) compiled against this delivery by deliver3.py: 13 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LocallyFiniteAdicCoefficientPresentations": "07f07f6c7d45155f1d455d2d917ace87570bc99a", "Sheaf.Paper.LocallyFiniteAdicCoefficientSystem": "32b77a164b4c3c86715b841e2c3c4504fc23f865", "Sheaf.Paper.LocallyFiniteAdicFiniteCocone": "a2012cfd10584e109579789991a33ec8f7722607", "Sheaf.Paper.LocallyFiniteAdicNormalizedFunctor": "f8d107c50df3246c3a5e02d64d6fd5631d917109"}, "results": {"Sheaf.Paper.AdicCompletedTensorFiniteModels": {"hash": "c5f8e01c0e737e878997f2f5c62ec19d035201e0", "status": "OK"}, "Sheaf.Paper.LocallyFiniteAdicConstructibleRealization": {"hash": "916ef6335a84737c7a527093bbdbd2477d597084", "status": "OK"}, "Sheaf.Paper.NativeAdicFiniteNormalization": {"hash": "891068305d0d87a67171418a42534d5dfc23eab0", "status": "OK"}, "Sheaf.Paper.SfAdicCommonStageDescentEquivalence": {"hash": "3cef5ea1f2ac78bc6ac6380937ca9dc32b367198", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares": {"hash": "2943a9fc6fd129f8289051e2740553ab4f9defcc", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalForgetful": {"hash": "558d68376aa151c040c27a8900d7ec63bc19178f", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalForgetfulData": {"hash": "689f4dff827e0634508a8c7747796789416b8331", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalLeftModels": {"hash": "4d6553f2ef3e08a14148f5f9c538d37140827f2b", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit": {"hash": "38d8da350553c21ab8acf4601f5ef60e14e4c474", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison": {"hash": "26ba422a92afc87589cff07312e37d42ac197d32", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness": {"hash": "6d9ff825e9bb3fda66d8f1af50c3c594981792d5", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalStructuralTransport": {"hash": "a1a57585bab7bb93d68e3bfe8211d452b147e948", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDual": {"hash": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5", "status": "OK"}}, "seconds": 101, "time": "2026-10-28T08:21:31+0800", "transitive": 12, "version": 1}
```

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
