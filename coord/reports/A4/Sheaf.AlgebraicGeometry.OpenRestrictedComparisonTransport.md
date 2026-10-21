## What changed

Withdraw the redundant historical module
Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport using deleted.txt.
Redirect its sole live consumer,
Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport, directly to
WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonTransport.
Only that private import line changes; the consumer's signature and complete
proof remain byte-for-byte unchanged. No adopted source file changes.

Keep lem-pc-open-restricted-comparison-transport attached to the canonical
upstream theorem, and keep its parent dependency and its two proof dependencies.
Update both nodes' proof-origin explanations and the parent's first proof step
to record the direct canonical import and historical wrapper withdrawal.

Change record: coord/changes/A4-open-restricted-canonical-consumer.md.

## Proved and sorry left

Closed: none, 0 of 0 holes in the assigned module. Added: none.
Split off: none. No sorry remains in the delivered consumer or the withdrawn item stub.
The canonical theorem
AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_transport
already has a complete proof combining exists_open_restricted_representative_data
and exists_open_restricted_comparison_square. The consumer theorem
AlgebraicGeometry.SingleComplexBaseChange.exists_open_comparisonIntoPullback_transport
also remains completely proved. This is a module-retirement delivery with zero
net holes, not a claim of a newly proved theorem.

Validation: the adapted consumer compiles with no warnings in 38.6 seconds.
A scratch check reproduces the complete historical transport signature with
IsAcyclicTensorKFlat, applies the canonical theorem with all arguments unchanged,
and proves equality with IsKFlatTensor by rfl. The canonical transport theorem
prints only propext, Classical.choice and Quot.sound as axioms. Scratch checks
are excluded from the delivery. Both node proof_deps lists equal the union of
their proof-step uses; all mathematical dependencies are preserved.

## No longer needed

The historical re-export module
Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport is no longer needed:
its only live importer now uses the adopted source provider directly. The
module is explicitly withdrawn in deleted.txt; no declaration or DAG node is
withdrawn. Its three redundant public imports disappear with the wrapper, while
the consumer retains its own public naturality/Arrow imports and the canonical
provider retains the public composition-map import. No other module is pruned.

The item node and its mathematical dependencies
lem-pc-open-restricted-representative-data and
lem-pc-open-restricted-comparison-core are still required by the canonical
proof. The parent still cites lem-pc-open-restricted-comparison-transport; its
proof route and the unit's realized statement and steps remain intact.

## Where the brief, the DAG or earlier work was wrong

The assignment was overtaken by W6's independently reviewed restoration in
landing 20261021T162130-L-292211, immediately before A4's claim. The current
source is already a zero-hole canonical re-export, so restoring the old
quarantined duplicate or claiming to close a sorry would be incorrect. The
current retire-items.tsv also lists this historical path for replacement by
the canonical provider. This delivery completes that migration at its actual
consumer and withdraws the extra import path, rather than submitting a no-op.

The old quarantine archive ceased to exist in the refreshed shared snapshot
while work was in progress; the live item remains present. deleted.txt names
that existing live item, never an already-absent quarantine path.

Searches performed with msearch.py: grep for
exists_open_restricted_comparison_transport (0 Mathlib hits); leanfinder for
derived stalk comparison and open restriction (8 ordinary restriction/stalk
hits); loogle for AlgebraicGeometry.Scheme.Modules.restrictFunctor (12 hits).
Direct library search found the exact complete adopted theorem, which is the
shortest route. No new mathematical statement or node is introduced.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
