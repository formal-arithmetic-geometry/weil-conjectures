## What changed

Proved `WeilConjectures.IntegralSystemRealization.ordinarySystemPullbackCompositorEvaluation`
in `Sheaf.Paper.OrdinarySystemPullbackCompositorEvaluation` by direct adjunction mate
pasting. The proof identifies the inverse evaluation comparisons as mates using their
existing unit specifications, proves the direct-image evaluation square on sections,
and transfers that square back through Mathlib's injective mate correspondence.

The intrinsic compositor section calculation uses the proved unrestricted
`finite_comp_mate` helper of `Sheaf.SixFunctors.AmbientAdjunctionCompositorNormalization`
and the proved section-realization helpers of
`Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation`. Both imports are private
proof imports. All added helpers in the item are private and proved. Local irreducibility
attributes keep coefficient sheaves and their sheafification choices folded during
section calculations. The private `directEvaluation` and `baseComp` wrappers give
existing constructions explicit functor types; they introduce no new choices. Updated the item's DAG
proof, proof dependencies and proof origin to this route.

Validation: the full proof compiled with server `lcompile.py` in 28.2 seconds.
Removed the profiling options and scratch module before delivery. Checked the
public signature against both the original source and its DAG record; it is identical.
Both added proof imports are used. All Lean lines have at most 100 characters.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.IntegralSystemRealization.ordinarySystemPullbackCompositorEvaluation`
(node `lem-pur-ordinary-system-pullback-compositor-evaluation`).

Holes closed: 1. Holes added: 0. Holes left in the delivery: 0. No split-off statements.
The statement, including all universes and hypotheses, is preserved. The calculation
uses arbitrary sections and applies to zero modules, empty schemes, identity morphisms
and n=0. No finite-type or ground-field assumption is used by the imported ordinary
helpers.

## No longer needed

Removed `lem-pur-ordinary-pullback-composition-evaluation` from this node's proof
dependencies. Its module `Sheaf.Paper.OrdinaryPullbackCompositionEvaluation` is not
imported: direct mate pasting avoids identifying the alternative sequence pullback
presentation and its compositor. This is a dependency pruned from this proof;
the declaration and its other users remain in the library.

No existing Lean import was removed. The existing statement dependencies, including
the intrinsic open-square and completed comparison definitions, remain necessary.
No other node, module or unit step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned invocation of the unfinished `ordinaryCompositionEvaluation` theorem is
unnecessary: its ordinary normalization argument can be performed directly for the
specified operations using existing proved helpers. The original theorem docstring
records that earlier plan; the updated node and this report record the implemented
proof.

The current server queue lists this as a one-hole proof item. Its historical build-error
record reports a bad import of `Sheaf.SixFunctors.IntegralSystemOperations`, while the
rework record records a quarantined dependency. The current item source compiles with
that public import against the published build; this delivery fills its actual proof
hole and preserves the source and its attachment.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.OrdinarySystemPullbackCompositorEvaluation": "2866053e99ecfd11a08c1d71b446186701d435be"}, "results": {"Sheaf.Paper.SystemPullbackCompositorEvaluation": {"hash": "64a33c44e149badf5d451149b567595b86a8651d", "status": "OK"}}, "seconds": 61, "time": "2026-10-28T01:27:57+0800", "transitive": 0, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
