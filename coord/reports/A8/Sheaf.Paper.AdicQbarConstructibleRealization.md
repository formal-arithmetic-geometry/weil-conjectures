## What changed

Proved WeilConjectures.AdicQbarRealization.adic_qbar_constructible_realization from
existing library declarations, with no new theorem holes. The proof reuses the native
compact-support realization on the identity compactification to obtain both the native
Realization and its sectionFunctor equivalence. It then applies completed-tensor descent,
the fixed normalized common-stage closed structure, ambient evaluation comparison
and isomorphism normalization.
Three fully proved private helpers perform the objectwise assembly.
Validation: the definition/normalization pair compiles, and the final theorem
compiles cleanly against that overlay (9.8 seconds). All choices occur
inside theorem proofs; no data definition is chosen from an existence assertion.

Moved GeometricSpace, SpaceData, integralRealizationAgreement, FamilyCore and Family
unchanged to Sheaf.Paper.AdicRealizationFamilyData. The item publicly reexports the new
owner. AdicRealizationIsomorphismNormalization imports the definition owner instead of
the item. Its theorem statement and proof are unchanged. This repairs the existing
parent/dependency import cycle noted by the stage-2 independent reader. Updated the
existing definition node's lean attachment and the existence node's proof/dependencies.

Change record: coord/changes/A8-adic-realization-family-interface.md.

## Proved and sorry left

Closed 1 of the item's 1 original holes:
WeilConjectures.AdicQbarRealization.adic_qbar_constructible_realization
(lem-sf-adic-qbar-constructible-realization).

Added 0 holes. The item has 0 remaining sorry declarations. The unchanged sorry in
the adapted dependency is
WeilConjectures.AdicQbarRealization.adic_realization_isomorphism_normalization
(lem-sf-adic-realization-isomorphism-normalization). It remains the next stage-3 item.
The new family-definition module has no holes. The private native-realization, tensor-evaluation and tensor/Hom assembly helpers
have complete proofs.

## No longer needed

The item no longer directly uses lem-sf-adic-finite-realization-cocone or
lem-sf-adic-common-stage-descent-equivalence: their underlying realization work is
already packaged by lem-sf-locally-finite-adic-compact-support-realization, and the
latter also supplies the missing ordinary section-module equivalence. Their modules
are not imported here. This does not withdraw either node or any downstream dependency:
other proofs can still require them, including the tensor/Hom dependency plans.
Likewise the item need not directly import lem-sf-adic-common-stage-hom-transpose:
podCommonClosed_existsUnique already supplies exactly the fixed normalized closed
structure, and its evaluation formula is elementary from parameter naturality. The
ambient-Hom lemma's own dependency plan still cites that result.

The normalization module's public import of AdicQbarConstructibleRealization is replaced
by the new definition owner to remove the cycle. The item's original four public imports
are retained transitively in that owner. No mathematical module is withdrawn or globally
claimed prunable; no source-library declaration or public source import is changed.

## Where the brief, the DAG or earlier work was wrong

The isomorphism-normalization module needed Family from its own parent's module,
creating a cycle as soon as the parent used its planned lemma. The stage-2 review
already identified this; moving the existing definition package makes the intended
proof dependency usable.

The six-step dependency interface did not directly supply a theorem asserting the
sectionFunctor equivalence required by the normalization and ambient-Hom lemmas.
The existing native compact-support realization supplies it together with the
objectwise Realization, so no new assertion is introduced. The generic tool dependencies
are acyclic with the item and preserve the unit's route. The unit's realized statement
and proof-step lists are empty, so no fixed unit step is bypassed.

The completed tensor result deliberately has no Hom-isomorphism field. The proof first
uses its tensor-only data as TensorInput, obtains Hom invertibility from the ambient
comparison, and only then builds At. Its finite normalization fields are retained
verbatim. The source is the already fixed podCommonClosed with its published finite
normalization; the tensor-evaluation identity follows from parameter naturality,
and the realized transpose law follows by cancellation.

The rework table lists older quarantine paths, but the current source modules are
present. Their definitions and Lean attachments are preserved, with the five definition
attachments relocated explicitly rather than removed. No quarantine file is deleted.

A refreshed downstream audit also finds AdicProperAdjunctionRealization,
NativeProperCoefficientOperations and NativeProperTensorComparison. Their public
imports of the item still expose exactly the same family definitions; no adaptation
is required. The change record lists them.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
