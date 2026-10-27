## What changed

Prove `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.internalSection_tensorLocalization`
from ordinary section-action coherence, coherent derived monoidal descent of an exact
monoidal equivalence, and the native ringed tensor-Hom adjunction. Summand extensionality
identifies the fixed total comparison with the inverse native complex tensorator.
Monoidality of the localization factor gives the square; on K-flat section images,
cancel its invertible target localization tensorator. Repeat on each actual slice
and transport across the equality with the literally restricted section ring.

Repair the unclaimed `InternalSectionTotalComparison`,
`InternalSectionDerivedTensorComparison`, `InternalSliceDerivedHomComparison` and
`InternalSectionScalarHomTransportData` interfaces so these concrete arguments compile
against the shared direct functor without expanding their large data.
The full old/new definitions and consumer audit are in
`coord/changes/w7-internal-section-ordinary-comparison.md`.

The ordinary coequalizer comparison and its signed total comparison are named at a
generic site before coefficient specialization. Their public pure-tensor and summand
equations retain their complete normalization. `SectionTensorTotalData.unique` proves
that the mapped total summands determine the entire chosen record. No arbitrary
existence witness supplies new data. The unchanged native coefficient monoid is named
once with instance transparency. Public sheaf-composition and commutativity bridges
retain the canonical structures; the direct and symmetric-parent braidings agree by `rfl`.

`sectionForward` names the primitive forward section functor.
`sectionForward_eq` identifies it reflexively with the recorded equivalence functor.
The global `forward`, `complexForward` and `localizationIso` use this primitive functor
directly, with the same values as their former bodies. Proved additive and equivalence
instances accompany the direct functor; `equivalenceAdditive` retains the recorded
equivalence's inferred additive interface.

`totalComparison` directly uses the constructed complex map. The slice ordinary and raw
total maps use the same generic API. The literal slice total map casts that actual raw
map along `sliceTotalComparison_type_eq`; `sliceTotalComparison_heq` retains the whole
map, and its existing unique characterization follows by HEq transitivity.
`sliceRawComplexForward` and `SliceRawComplexTensorType` share its actual endpoints.
`sliceTotalTensor` names the unchanged native total tensor.

Both normalization predicates retain exactly their former expanded HEq formulas through
`tensorLocalizationSquareHEq`. Named endpoint types and generic two-field records retain
exactly the original global/slice isomorphism and normalization data. Consumers use field
notation; none uses the former qualified constructor, recursor or projection names.
`totalComparison_heq` and `sliceEquivalence_functor_heq` expose the concrete equations
needed by localization. The private normalization record distinguishes the iso's
dependence on the closed structure from the square's additional dependence on models.
Its generic elimination lemma produces the required existential packages.

No adopted `WeilConjectures` source module is edited, and no target statement changes.
These definition repairs are submitted for independent target-interpretation review.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.internalSection_tensorLocalization`:
one hole closed, zero added, zero split off. There are zero `sorry` occurrences in the
seven delivered Lean files without existing holes. The eighth file, the proof-adapted
continuity consumer
retains these six existing named holes (none added): `homPresentation_nonempty`,
`internalScalarHom_identity`, `internalScalarHom_composition`,
`scalarTransport_composition`, `restricted_hom_transport` and
`internal_section_hom_continuity_comparison`, all attached to
`lem-sfb-internal-section-hom-continuity-comparison`. Every added helper is proved.

The completed theorem's `#print axioms` check lists exactly `propext`, `Classical.choice`
and `Quot.sound`. The four repaired/core modules compiled as a batch within the per-file gate.
The direct-consumer batch also passed: `ModuleObjectRingedSiteDerivedComparison`,
`FiniteFreeDualChainModels`, `FiniteFreeOrdinaryChainComparison`,
`NativeOrdinaryEvaluationLocalization` and `FiniteFreeDualChainComparison`.
An independent importing probe checked the three global aliases against their old
bodies by reflexivity, both normalization predicates against their full original
expanded HEq formulas by reflexivity, and the adapted representative counit against
its original expression by reflexivity. The target signature is unchanged byte for byte.
Further unchanged consumers passed: `GeneralLfpAdicInputWitness`,
`InternalSectionMonoidalNormalization`, `ProfiniteFreeSliceDerivedHom`,
`StrictCompletionRestrictionData`, `InternalSectionScalarHomTransportData` and
`StrictSectionQuotientTensorModels`. Freshly rebuilding `NativeDerivedRestrictionData`
also passed. `StrictSectionPrincipalQuotientModels`, `ProEtaleDerivedRestrictionClosed` and
the adapted `InternalSectionHomContinuityComparison` also passed. The final
`InternalDerivedClosedLocalization` consumer also passed with freshly compiled
normalization and restriction prerequisites. All consumer checks passed. `InternalSectionScalarHomTransportData` is adapted to express its canonical derived
restriction normalization through the direct `sectionForward` API. The same functor
and normalization formula are retained definitionally, checked by applying the
new normalization field directly to its old expanded statement. This also ensures the
independent per-file checks use freshly compiled normalization data instead of the
published artifact containing former generated `ring._proof_6`/`ring._proof_7` names.
Other temporary validation copies are excluded from the delivery.

## No longer needed

The proof does not use these original DAG proof dependencies:

- `lem-sfb-exact-monoidal-equivalence-total-kflat`
  (`Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat`): coherent derived descent
  already incorporates the equivalence's flat-preservation and representative argument.
- `lem-pur-derived-tensor-comparison` (`Sheaf.CategoryTheory.DerivedTensorComparison`):
  the monoidal localization factor supplies the square directly.
- `lem-sfb-exact-tensor-functor-derived-normalization`
  (`Sheaf.CategoryTheory.DerivedCategory.ExactTensorNormalization`): the descended strong
  monoidal structure already gives invertibility.

These were DAG dependencies, not original imports. They may remain needed elsewhere;
no module or DAG node is withdrawn. Both original public imports remain.

The duplicate slice helpers `sectionTensorWitness`, `sectionOrdinaryTensorIso` and
private `sectionRawTensorComparison` are removed. Their only use was to select a second
copy of the same normalized maps. The shared generic API supplies those maps and their
formulas. The proof-only `import all` of the slice module is unnecessary; the public
transport equations suffice. No redundant direct total-module import is added to the
localization module, since its public derived-comparison import already provides that API.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but longer than needed. Coherent descent already proves
the abstract monoidal localization statement; its square and the summand equations
supply this reduction without new K-flat comparison statements. The compile bottleneck
was repeated expansion of concrete definition data. Generic records, named endpoints
and proved equations address it without splitting the proof or raising the time limit.
The proof applies to empty sites, zero rings and arbitrary unbounded complexes without
additional hypotheses.

## Forced adaptations

Both adapted consumers are unclaimed. Their existing signatures, visibility and public
imports are unchanged; neither adaptation adds a hole.

`ModuleObjectRingedSiteDerivedComparison`, `globalHomIso`, lines 358-363:
the original call supplied `(equivalence Λ X).mapDerivedCategory` and failed with
`Application type mismatch: t.iso has type GlobalTensorComparisonIsoType Λ X S`
where the expected tensor-comparison type used that recorded equivalence's derived
functor. The consumer locally seals `sectionModuleEquivalence`, hiding its reflexive
agreement with the new direct forward alias. Add the proved local
`(forward Λ X).IsEquivalence` instance and supply `(forward Λ X).asEquivalence` instead.
This gives the generic closed-equivalence argument its exact forward endpoint and
leaves the mathematical proof and public statement unchanged. The original failed
and the adapted module compiled successfully.

`InternalSectionHomComparisonData`, `homRepresentativeIso`, lines 188-194:
the original `representativeCounit` term failed with `Type mismatch`, producing the
recorded complex-equivalence functor where `internalHomRepresentative ⋙ complexForward`
was expected. This consumer also locally seals `sectionModuleEquivalence`.
Explicitly simplify with `sectionForward_eq`, the definitions of the representative
and direct complex functor, and `Equivalence.mapHomologicalComplex`. The constructed
map is still the original equivalence counit, with the same signature and normalization.
The original failed and the adapted module compiled successfully. An independent
importing probe also proved equality with the original counit expression by `rfl`;
its axiom list contains only the three allowed axioms.

`InternalSectionHomContinuityComparison` (unclaimed) failed at four endpoints:
`termwise_lower_bound_iff` expected the direct complex functor, but `hz` supplied the
sealed recorded equivalence functor; `cohomological_lower_bound_iff` had the same
mismatch for the derived functor; `continuity_iff` supplied `homRepresentativeIso`
with the direct complex functor where the recorded equivalence functor was expected;
`scalarTransport_identity` supplied `t.derivedRestriction` with the direct derived
functor where the generic ringed identity theorem expected its recorded presentation.
Use the direct section functor in the first two bound proofs (lines 606-622),
its `asEquivalence` and proved additive instance in continuity (lines 704-713),
and locally expose the recorded equivalence in the scalar identity proof
(`IdentityTransport`, line 1166). Existing signatures and visibility stay unchanged.

The adapted continuity consumer compiled successfully. Its original four mismatches
are preserved in the validation result; fresh prerequisite builds also eliminate
old generated proof-constant references from the published artifacts.

The original continuity diagnostics were:

- line 610: `Type mismatch: hz (P.X n)` had endpoint
  `(equivalence Λ X).functor.obj (P.X n)` instead of `((complexForward Λ X).obj P).X n`;
- line 622: `Type mismatch: lowerBound_transport (equivalence Λ X).functor K b`
  had the recorded derived endpoint instead of `(forward Λ X).obj K`;
- line 709: `Application type mismatch` at `homRepresentativeIso Λ X P`, whose
  direct complex functor did not match the sealed recorded functor expected by
  `continuity_equivalence`;
- line 1188: `Application type mismatch` at `t.derivedRestriction`, whose direct
  derived forward endpoint did not match the recorded endpoint expected by
  `ringed_identity_transport`.

These are elaboration changes only; the direct and recorded functors have already
been independently checked equal by reflexivity.

`InternalSectionScalarHomTransportData` is unclaimed. Its two functor arguments in
`ScalarTransport.restrictionNormalization` (lines 224 and 226) now use `sectionForward`
for the same exact functor. No field is added or removed, and no map in the canonical
localization composite changes. The old statement was independently checked using
the new field without casts or additional assumptions (compiled successfully).

Reproducing the delivery axiom probe with the repaired scalar-data overlay reports
`SHEAF-PROBED 23`, exactly the six existing named sorries, and no `SHEAF-AXIOM`.
The separately appended diagnostic probe adds overhead beyond the already-passing
58.7-second normal consumer compile; the delivered source contains no diagnostic probe.
The prior self-named-axiom diagnostics were placeholders following stale-artifact
kernel errors, rather than new axioms or a mathematical dependency problem.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
