# AlgebraicGeometry.schemeHomOriginalTensorPullbackIso (new API, partial repair)

## Reason

The repair inventory identifies two legacy wrappers that select data relative to
a freshly chosen composition counit. A counit twist changes their literal Hom
equivalence and tensor comparison. The original derived-pullback witness must be
retained as the normalization datum.

## Old

The public legacy adjunction and tensor are chosen from the composition-counit
specification. These existing definitions, signatures and all caller-facing
statements remain VERBATIM in this delivery. The proof of the existing tensor
existence theorem is shortened using the same monoidal realization.

## New

In the new module `Sheaf.AlgebraicGeometry.GlobalHomOriginalCounitNormalization`,
add a concrete extraction of the original presentation, its universal counit,
a derived adjunction normalized to it, and the tensor iso transported by the
unique counit comparison. Prove both counit equations, the ORIGINAL-counit tensor
predicate. The inverse counit equation and existing canonical uniqueness theorem
provide the mathematical uniqueness argument after reversing the transport. There are no new proof holes or arbitrary witnesses
of unproved mere existence. All supporting constructions have proved properties.

## Users

The added API has no external users on the delivery base. Its new declarations
are used by this module's original-counit extraction, comparison and normalized
tensor proof. Existing declarations, including the global Hom maps, are unchanged,
so all existing users require no adaptation. The unchanged
`MixedTensorPairingBaseChangeTransport` caller was compiled against the final
sandbox artifact and passed; the earlier switched-definition experiment exposed
the normalization mismatch reported below.

The future coordinated users are `DerivedPullbackComposition`,
`SchemeDerivedBaseChangeMap` (held by D2), `MixedHomTensorPullbackIso` (unclaimed),
and `MixedTensorPairingBaseChangeTransport` (unclaimed). This delivery does not edit
any of them. No external caller-facing definition or statement changes. The original module has only the tensor-existence proof simplification,
and its node is unchanged; the new node owns the normalization API.

## Remaining coordinated work

Switching the old adjunction alone breaks the original base-change-mate proof in
`MixedTensorPairingBaseChangeTransport`, line 87. Baseline source compiled; against
the changed adjunction its `change` is not definitionally equal to the goal.
That goal compares the old base-change mate with the new adjunction, so a fake
compatibility lemma must not be introduced. Switching only the tensor also changes
the global Hom mate's normalization. The production definitions therefore remain
unchanged until upstream composition, base change and mixed tensor data are
normalized together. This delivery is a proved enabling step, not a completed
repair of the two legacy aliases.

`SchemeDerivedBaseChangeMap` is held by D2; `MixedHomTensorPullbackIso` and
`MixedTensorPairingBaseChangeTransport` are unclaimed. Neither they nor protected
SingleComplex modules are edited. No forced adaptation or claim acquisition is
included. Existing target definitions and meanings stay unchanged.

## Validation

Single-file compilation and delivery dry run passed; the second reader then
invokes the required delivery command. No global build or lake invocation. See report.md for final validation and the original-counit
normalization/edge-case argument. The independent reader should review this as a
partial repair and keep the legacy-normalization repair outstanding.

## Status

landed 20261014T043533-L-1336481 2026-10-14 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso)
statements and data definitions are unchanged; the added API is public.
