# Module.exists_elementary_generating_tuple_change: private helper scopes

## Reason

The proof introduces private elementary-operation constructions and proved helpers.
The static interface check flags the new `variable` and `omit` commands. They occur
inside `section TupleHelpers`, which ends before the original public theorem.
They control only the binders of the new private declarations. The public theorem's
signature, all imports, and all existing visibility and attributes remain identical.
No new global instance, notation, or simplification attribute is introduced.

## Old

There was no helper section, no section variable, and no `omit` command. The commands
outside declarations, as recorded by the static interface checker, were:

```lean
@[expose] public section
set_option autoImplicit false
universe u v
open scoped BigOperators
```

## New

The original commands remain verbatim. The private helpers add the following scope:

```lean
section TupleHelpers

variable {R : Type u} [CommRing R] {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable {M : Type v} [AddCommGroup M] [Module R M]
```

The command `omit [DecidableEq ι] in` precedes each of
`TupleOp.embed_act_fixed`, `tupleRun_embed_fixed`, `quotient_tail_span`, and
`tupleMatrixAct_mul`, all private proved theorems. The section closes with
`end TupleHelpers` before `exists_elementary_generating_tuple_change`.
All private definitions contain explicit constructions and all their required
proofs are complete. The public theorem now has a complete proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.RingTheory.LocalGeneratingTuples` | B4 | Assigned module; one hole proved; private helpers added. |
| `Sheaf.RingTheory.CompletionRegularKernelPreservation` | unclaimed | Direct importer; no signature, instance, or import change; no adaptation. |
| `Sheaf.Paper.PurityFrameIndependence` | A4 | Direct importer; no signature, instance, or import change; no adaptation. |

Neither direct importer currently mentions the public theorem by name; both retain
their own unfinished proofs. All transitive importers continue to see the identical
public declaration and imports. No target statement or definition used by a target
changes, so no target meaning is reopened.

## Status

landed 20261019T231040-L-542686 2026-10-19 (merge of deliver/B4/Sheaf.RingTheory.LocalGeneratingTuples)
