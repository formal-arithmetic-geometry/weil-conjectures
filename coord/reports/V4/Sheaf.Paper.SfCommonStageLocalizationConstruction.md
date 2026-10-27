## What changed

Filled `WeilConjectures.sfCommonStageLocalizationConstruction` with a complete proof from the
existing `ExceptionalCommonStage.exceptionalCommonStageDescent` theorem and the new, strictly
finite-stage `sfSupportedLocalization_finite_coherence` obligation. Existing public signatures,
public imports, definitions, and targets are unchanged. Only sandbox files were written.

The private `localizationPullbackEquality` proves equality with the canonical common-stage
pullback by its unique object/representative specification. Its argument follows the existing
private helper in SfQbarLocalizationCommonStage, generalized to arbitrary residue-invertible
schemes; that module's public theorem requires a finite-field datum, which this item does not.
The private `supportedOfDescent` constructs the supported record: boundary uniqueness follows
from triangle_morphism_extension, the descended closed counit is invertible by its finite-stage
normalization, and full faithfulness makes the exceptional unit invertible. The exceptional
adjunction and shifted orthogonality make the endomorphisms of exceptional(openPush G)
a subsingleton, hence that object is zero. The private `stageComparisonOfDescent` proves all
three scalar unit/counit equations using the identity components of ιCompFunctorIso and the
actual Descent normalization equations. The main proof assembles precisely the required record.

The new finite coherence theorem does not assert any common-stage functor, adjunction,
distinguished triangle, Hom action or comparison with the common-stage pullback. It only
connects the supplied rational localization records to the finite hypotheses of the existing
descent theorem. All the common-stage construction and remaining categorical consequences
are proved in the assigned module, so this is not the original statement under another name.

The item's node now follows these Lean steps. The new node records the finite coefficient
coherence part of step 12, its complete proof in words, source and the searches actually run.
The generic rational direct-image coefficient compatibility node is an auxiliary tool for this
remaining finite step; it applies to arbitrary supplied right adjoints and does not replace a
unit route. The supported-localization unit's route is retained.

## Proved and sorry left

Closed one existing hole: `WeilConjectures.sfCommonStageLocalizationConstruction`
(node `lem-sf-common-stage-localization-construction`). The assigned module has zero holes.
All three private theorem proofs and the private record construction are complete.

Added one hole: `WeilConjectures.sfSupportedLocalization_finite_coherence`, in
`Sheaf.Paper.SfLocalizationFiniteCoherence`
(node `lem-sf-supported-localization-finite-coherence`). Its complete proof is exactly
`:= by sorry`; its source and proof in words are in its docstring and node.

This is a decomposition, with one hole closed and one hole added, net zero. The existing
`ExceptionalCommonStage.exceptionalCommonStageDescent` and previously holed specification
theorems retain their own holes unchanged. No hole is introduced inside a definition.

## No longer needed

Removed the item's direct private import `Sheaf.Paper.PbcScalarExtension`: no declaration from
it is invoked directly by the final assembly. Its scalar compatibility results remain relevant
to the finite coherence obligation, and the module remains publicly imported by
ExceptionalCommonStageDescent. Thus this is not a claim that PbcScalarExtension is pruned
from the targets' closure. The item's old direct proof edge to
`prop-weil-pbc-scalar-extension` is replaced by the new finite coherence step, which retains
that dependency.

No existing node or module is withdrawn or globally pruned. The explicit descent dependency
and its module remain necessary. The triangle-morphism-extension dependency is now explicit.
No unrelated finite-field-only localization module is imported.

## Where the brief, the DAG or earlier work was wrong

The earlier one-step plan does not directly instantiate exceptionalCommonStageDescent:
SfRationalLocalization stores no coefficient-system morphisms, no compatible shift structures,
and no canonical scalar mate equations. These are genuine additional finite-input obligations,
now isolated rather than hidden in the common-stage record construction.

No statement is disputed or weakened. Edge-case checks of the new statement: for empty U,
open functors and boundary reduce to zero and the closed/exceptional adjunctions give the
identity case; for empty Z the open adjunction supplies the identity case and the exceptional
functor is zero. The coefficient identity case uses the actual scalar unit, not a claimed
literal equality of unnormalized tensor functors. Arbitrary base fields and both coefficient
universes are retained. Arbitrary supplied adjunction normalizations are handled by conjugating
canonical comparisons through their adjoint isomorphisms; no new compatibility is imposed
on the supplied rational records.

## New nodes

`lem-sf-supported-localization-finite-coherence` is attached to
`Sheaf.Paper.SfLocalizationFiniteCoherence` and states only the finite coefficient input
construction. Its proof uses the existing canonical rational pullback/right-mate coefficient
compatibility, scalar coherence, adjunction-compatible shifts, closed full faithfulness,
and ordinary open localization. Mathlib searches used LeanSearch, LeanFinder/Loogle and grep;
Mathlib supplies the categorical infrastructure but not this geometric coefficient package.
The related SfQbarLocalizationFiniteCoherence theorem constructs different, ordinary
open-closed data and requires a finite-field base; it does not apply here.

No change record is needed: existing public declarations, signatures, attributes and public
imports are unchanged, and all newly added helpers in the existing item are private.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
