## What changed

Proved `WeilConjectures.finiteDualizingRealizationRestriction_transport_core` in
`Sheaf.SixFunctors.FiniteDualizingRestrictionTransportCore` without changing its statement.
Two fully proved private helpers establish ordinary comparison-restriction composition
and its exact derived localization. Their argument follows the existing private
`ordinaryRestrictionComp` and `derivedRestrictionComp` proofs in
`Sheaf.Paper.NormalizedOriginComparisonCoherence`; the helpers are reproduced locally
because that module does not export them. No transparency-respect option is disabled.

Added the proof-only import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars` for its
proved `Functor.mapDerivedCategorySquareIso_hom_app_comp`. Cancellation of inverse
comparisons, functoriality, and naturality of the intrinsic restriction comparison finish
the proof. Updated the item's node to describe this argument. The public interface,
all definitions, and the unit route are unchanged. No other existing module is edited.

Validation: the final single-file `lcompile.py` run compiled cleanly in 18.6 seconds,
within the 60-second limit. The original theorem signature is byte-for-byte unchanged;
the file has zero textual holes and every line is at most 100 characters.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.finiteDualizingRealizationRestriction_transport_core`
(node `new-finitedualizing-restriction-transport-core`).
No holes remain in the item, and no holes or split-off statements are added.
The two private helpers are fully proved.

## No longer needed

Removed `lem-coef-dualizing-intrinsic-restriction-comp` from this node's proof dependencies.
Its module `Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionComp` is unnecessary for
this proof: naturality of the one intrinsic restriction comparison suffices. Other parents
still use that theorem, so this is a pruned proof dependency, not withdrawal of the module.
The original sole public import is retained because it supplies the statement's data.
No previously present Lean import was removed; the new proof-only import is used.

## Where the brief, the DAG or earlier work was wrong

The original node listed intrinsic restriction composition as a proof dependency, but the
core square needs only intrinsic restriction naturality. The remaining ordinary and derived
comparison composition argument already existed as fully proved private helpers in
`Sheaf.Paper.NormalizedOriginComparisonCoherence`. This closes the core rather than
splitting it again. The statement handles identity/repeated levels and the first finite
coefficient level using the same general ring-map argument; no strict inequalities,
flatness assumptions, or nonempty-site hypotheses are introduced.

Current server records were checked: the queue lists an ordinary one-hole proof item,
the claim belongs to J2, and there is no rework entry or build-error file for the item.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingRestrictionTransportCore": "6378e19811fb7b7c1ee488a6041c5bda5399c1f0"}, "results": {"Sheaf.SixFunctors.FiniteDualizingRestrictionTransport": {"hash": "24e6f8a67b06ce663e08cea7768d261a649fe612", "status": "OK"}}, "seconds": 133, "time": "2026-10-28T10:24:06+0800", "transitive": 0, "version": 1}
```

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
