## What changed

The main scalarExtensionTowerCoherence theorem now obtains completeness of completed
pullback and tensor from integralOperationRoos_effectivity on good representatives. It assembles its two
whole-system equations by naturality of the coherent reduction/limit counit.
A proved private generic lemma carries out the equation
R(a) R(x) epsilon t = R(y) epsilon s from a x L(t) = y L(s).
This is a decomposition of the comparison-normalization work, not a net proof of a hole.

Two new modules isolate the genuinely separate pullback and tensor limit-coordinate
calculations. The pullback lemma has no tensor models or second input. The tensor lemma
has no morphism of schemes, Bool-indexed operation family, or pullback model. Each states
a comparison in the completed-coefficient derived category before adjunction, while the
item proves both required system-category equations by counit naturality.

To avoid import cycles, ScalarExtensionTowerRealizationData contains the existing block
from integralTensorGenerator through derivedSigma verbatim, including the already proved
derivedSigma_existsUnique. The original module publicly re-exports it and retains every
original public import. No existing signature, definition body, instance, global attribute,
source-library declaration, target, or unit route changes. The change record is
coord/changes/B4-scalar-realization-data-relocation.md. The definition-node ownership
remains through the original public re-export; the relocated derivedSigma theorem has a
new statement node recording its existing complete proof.

Profiling also identified expensive section-type conversions in the already proved
quotient-model generator criterion. The unchanged `modelSection` and that proved
criterion are isolated in `ScalarExtensionQuotientSectionExt`, publicly re-exported
by the item. The criterion is now the public `quotientModelSection_hom_ext`; the
`quotientModels` caller is updated. Its new node records the existing proof. This
module respects default transparency; no profiling settings are retained.

Validation: the final clean item compile passed without diagnostics in 38.3 seconds.
The final quotient-section module compiled in 13.3 seconds, and the three other new
modules also compiled successfully. All five direct importers were
checked unchanged: AdicCompletedTensorRealizationDescent (38.6 seconds),
CompletedComparisonQuotientRealizationDefs (49.7), IntegralComparisonSystemData
(45.8), IntegralScalarPullbackCounitCompatibility (9.9), and the final clean
RationalRealizationTensorComparison (35.2). Temporary consumer copies and all profiling
settings have been removed from the delivery. The extracted data block was checked
verbatim, every original public signature is retained, and node proof dependencies
match the stated proof steps.

## Proved and sorry left

Closed by decomposition: WeilConjectures.ScalarExtensionTower.scalarExtensionTowerCoherence,
node lem-pur-scalar-extension-tower-coherence. Its counit calculation, completeness witnesses,
and conjunction assembly are complete Lean. Original hole count: two. One original hole
remains: WeilConjectures.ScalarExtensionTower.realizationModels, at the same node.

Two holes are added, one named public theorem per new module:

- WeilConjectures.ScalarExtensionTower.scalarTowerPullbackLimitSquare,
  node stage3-pur-scalar-pullback-limit-square.
- WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare,
  node stage3-pur-scalar-tensor-limit-square.

Thus one original hole is closed, two are split off, and three actual holes remain in
this delivery. Holes closed minus holes added is minus one, not positive proof progress.
The relocated derivedSigma_existsUnique stays proved, as do square, unit, composition and quotientModels.
No data is chosen from an arbitrary unproved existence assertion and no definition has a hole.

The limit-coordinate lemmas were checked on their degenerate inputs: zero complexes,
empty schemes, identity coefficients and identity pullback. Their formulas use the actual
model isomorphisms and functor maps, include the whole tower and its transitions, and never
assume quotient coefficient maps are flat. They are strictly parts of the combined argument.

## No longer needed

The assembly needs only Roos effectivity for the completeness witnesses, so
lem-pur-integral-operations-preserve-constructible and its full constructibility
argument are unnecessary here. No new dependence on its proper-cohomological bounds
is introduced. The item privately imports IntegralOperationRoosEffectivity and
all of IntegralOperationsWellDefined to use the existing good localization.

The main theorem's assembly does not use the missing
Sheaf.Paper.NormalizedScalarComparisonRealization module. Its mathematical realization
existence route remains recorded for the original unfinished realizationModels theorem;
no absent or quarantined module is deleted or treated as withdrawn.

The proof imports TensorPullbackRepresentativeDescent, ResolvingRepresentativeWhiskering,
ChangeOfRingsKFlatIndependentCoefficients and CochainTensorUniverses move from the item to
ScalarExtensionTowerRealizationData, where the unchanged derivedSigma proof uses them.
The private proof import of CoefficientExtensionOrdinaryStrictTensor moves into
ScalarExtensionQuotientSectionExt, where its finite tensor generator criterion is used.
No original public import is removed. No node, module or adopted-source declaration is
withdrawn, and no unit route is bypassed. The new data module imports only its required
realization, completed-model and strict-comparison interfaces plus those proof imports.

The following direct parent proof edges are now carried by the relocated derived-comparison
proof instead: `lem-pc-kflat-resolution`, `lem-weil-pbc-resolving-representative-whiskering`, `lem-weil-pbc-tensor-comparison-descent-representatives`, `lem-pur-kflat-change-of-rings-independent`, `def-pur-scalar-extension-tower-data`.
The direct parent edge to lem-weil-pbc-ringed-strict-tower-homotopy-limit is no longer
needed for the counit assembly: total-limit functoriality is already in the two coordinate
steps. This does not withdraw that module from other proofs.

## Where the brief, the DAG or earlier work was wrong

The queue row is a proof assignment; the build-error file describes an older bad-import
failure. The current original item compiled successfully before edits (55.9 seconds), so
that stale build error is not this assignment's defect. The original had two holes, because
D3 had already closed quotientModels before this worker copied the current source.

The DAG's normalizedScalarComparisonRealization dependency names a module absent from
both the live source snapshot and the rework list. Existing reports D2, D3 and X7 already
record this. The two constituent normalization steps are stated explicitly here rather
than importing that unavailable module or claiming its construction exists.

STATEMENT-DISPUTED: realizationModels inherits the invisible-presentation-twist defect
reported by T6 for primitiveQuotientRealizationComparisons. The scalar normalization
quantifies over every finite-evaluation presentation isomorphism without the additional
whole-system coherence required by the repaired pullback normalization. The tensor
normalization has the same issue. Finite derived evaluations are conservative, not faithful
on morphisms. The T6 example uses a derived-complete nonseparated Z_p-module M and a
nonzero infinitely divisible x in M; on K=Z_p direct-sum M, the automorphism 1+delta sends
the unit in the first summand to x and has identity finite derived reductions. Twisting
a presentation by this automorphism preserves its finite conditions but changes the
normalization equation after total limit. This is a reported mathematical obstruction,
not a Lean-certified counterexample. The remaining existence hole and its signature are
preserved and flagged; this delivery does not attempt a shared normalization-definition
repair. The supplied-model hypotheses of the new conditional coordinate lemmas are
retained exactly. The current blueprint now describes integral operations intrinsically
and delegates reduction/scalar compatibility to sk-prop-scalar-six; these new steps
formalize that compatibility obligation without changing the existing operations.

An unpublished IntegralProperReductionBound dependency repeatedly fails monoidality
synthesis in its private integralLevel_isLE proof. Its current holder is B2, found
in coord/claims/Sheaf.Paper.IntegralProperReductionBound.lock. A checked proof-context
repair (27.2 seconds) is to add, inside that private proof:

```lean
  have : ((coherentTopology Profinite.{u}).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := coherentTopology Profinite.{u}) (A := Ab.{u + 1})
```

This repair is advice for the holder, not part of this delivery: the original already
fails independently of our changes, so it is not a forced adaptation.

## New nodes

stage3-pur-scalar-quotient-section-extensionality records the existing proved
whole-system generator criterion and the unchanged `modelSection` definition in
ScalarExtensionQuotientSectionExt. This extraction adds no hole.

stage3-pur-derived-scalar-tensor-normalization records the existing proved
derivedSigma_existsUnique in its new acyclic data module. Its resolving-representative,
change-of-rings and tensor-descent proof is unchanged. The old definition-node attachment
continues to describe the unchanged realization data publicly re-exported by the item.

stage3-pur-scalar-pullback-limit-square records only the pullback word calculation
in normalized total-limit coordinates. It neither chooses realization models nor proves
the tensor word calculation or either coherent-reduction equation.

stage3-pur-scalar-tensor-limit-square records only the tensor word calculation
in normalized total-limit coordinates, using the uniquely normalized derivedSigma.
It neither constructs models nor treats geometric pullback or coherent-counit assembly.

Change record: coord/changes/B4-scalar-realization-data-relocation.md.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 4 OK, 1 SLOW.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.ScalarExtensionQuotientSectionExt": "53ecc74e5f32f61778f9c6d6ee79231c7e6ae0e0", "Sheaf.Paper.ScalarExtensionTowerCoherence": "efb8bde570c7822a88e3957c16202b262f2277a6", "Sheaf.Paper.ScalarExtensionTowerRealizationData": "d6268383ff8fbbbe615f40cf68fd20e19912fff8", "Sheaf.Paper.ScalarTowerPullbackLimitSquare": "9b8e25d96f17214d7907bbec84a30465ce6559fe", "Sheaf.Paper.ScalarTowerTensorLimitSquare": "eb39c8230a4fbd499e5460ed3456e39a715f496f"}, "results": {"Sheaf.Paper.AdicCompletedTensorRealizationDescent": {"hash": "236ec29abf7bc268e4cd7a8533bab0f0622e6f0e", "status": "OK"}, "Sheaf.Paper.CompletedComparisonQuotientRealizationDefs": {"hash": "dfdfeed46ace6c4c802b28ac2734d71c9bcc5602", "status": "OK"}, "Sheaf.Paper.IntegralComparisonSystemData": {"hash": "6983e6f589bb81180a511d6f951b69864c960e26", "status": "OK"}, "Sheaf.Paper.IntegralScalarPullbackCounitCompatibility": {"hash": "e47f4da52bfc5ee0639fe24323f69ce5f789d3a6", "status": "OK"}, "Sheaf.Paper.RationalRealizationTensorComparison": {"hash": "fb60a875f5ff45bb9046ae9766520bd1ffded299", "status": "SLOW"}}, "seconds": 201, "time": "2026-10-28T00:54:13+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
