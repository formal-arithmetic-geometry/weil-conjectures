# Sheaf.Paper.PbcScalarExtension: private proof scopes

## Reason

The interface scanner conservatively flags the scope and local attribute commands
introduced for the three proofs in this delivery. This record describes those
commands. Every public declaration signature, definition body and public import is
unchanged. The new helpers are private and fully proved. The additional instances
and reducibility attributes are local to this module's proof sections, so importers
receive the same interface and mathematical objects.

## Old

There were no `NormalizedScalarAdjunctionShift` or `ScalarOperationShifts` sections,
no private generic completion-composition section, and no private scalar-restriction
shift instance. The new local attributes below were absent at these proof sites.
The three public theorem signatures are unchanged; their old proofs were `by sorry`.

## New

The normalized adjunction proof is enclosed by:

```lean
section NormalizedScalarAdjunctionShift
attribute [local irreducible] completedAdicDerivedChange pbcDerivedScalarAdjunction
```

Its scalar-restriction shift instance is private and locally registered. This scope
ends before the existing integral and rational shift definitions. The existing
`ScalarShift` and `NestedFields` sections also keep `pbcRationalScalarHom` folded via
`attribute [local irreducible] pbcRationalScalarHom`, after proofs which unfold it.

The operations shift proof is enclosed by:

```lean
section ScalarOperationShifts
attribute [local irreducible] completedAdicDerivedChange
```

The completed composition proof has an anonymous proof scope with:

```lean
attribute [local irreducible] pbcActualCompletedPull pbcActualCompletion
  reductionDerivedChange completedAdicDerivedChange
```

Each scope is closed in this module. Declaration-scoped transparency options on
private helpers permit comparison of the existing category aliases. The proof-only
imports are not public. None of these commands changes a target's meaning.

## Users

A read-only scan of the two library roots finds 1,504 transitive importers, including
`TargetsCheck`. None needs adaptation: there is no changed public signature, data,
instance, attribute or import to consume. All scoped reducibility and instance
commands are local and unavailable to importers. In particular, the generic private
lemmas only occur in public theorem proofs, never in public signatures or public
definition bodies.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcScalarExtension | M1 | Three proofs completed; local proof scopes only. |
| TargetsCheck | unclaimed | Same target and dependency statements; no adaptation. |

## Status

landed 20261022T025330-L-1282126 2026-10-22 (merge of deliver/M1/Sheaf.Paper.PbcScalarExtension)
