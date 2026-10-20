## What changed

Restored `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology`
from its quarantined source. Replaced its public import of
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` with
`WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel`.
All declarations and proof bodies remain verbatim. The existing proof still
composes first-factor and base/second-factor localization, proves comparison
compatibility by the scalar-map equality, and composes the naturality equations.

The repaired file was refreshed from the current shared quarantine source and
compiles through `lcompile.py` in 20.7 seconds with no warnings. Delivery validation also runs the project's axiom probe and preflight.
The change record is
`coord/changes/D5-derived-tensor-localization-upstream-model.md`.
No DAG change is needed: the theorem, proof route, and dependency nodes are unchanged.

## Proved and sorry left

This is the assigned upstream-sync build repair, with zero existing holes.
`RingTensorCohomology.derivedTensor_localization_cohomology`
(node `lem-pc-derived-tensor-localization-cohomology`) retains its complete proof.
Holes closed: 0 of 0. Holes added: 0. Holes split off: 0.
No `sorry` remains in the delivered module. No other Lean module is delivered.

## No longer needed

Removed import:
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`.
The upstream module with the same suffix supplies the canonical model used by
the localization lemmas. The Sheaf duplicate is no longer needed by this module;
its retirement and other users belong to the existing retirement process.
No mathematical dependency node is pruned and no global module pruning is claimed.
All three existing proof imports remain necessary. The unit record
`sk-thm-picard-semicon` has empty realized arrays; its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The item is a rework/build repair, not an unproved theorem. Its source is in
`quarantine/Sheaf/Algebra/Homology/DerivedTensorLocalizationCohomology.lean`,
not yet under `lean/`. The upstream sync migrated the proof dependencies to the
upstream model but left this module's public import on the Sheaf duplicate.
The recorded failure is a duplicate declaration during import, beginning with
`ModuleCat.BaseDerivedTensorCohomologyModel._sizeOf_inst`.
An independent compile of the original quarantined file reproduced that error
in 1.2 seconds. The two providers' complete model structure fields are
byte-identical. The consumer scan reports zero current library consumers;
quarantined consumers were inspected separately.
The existing proof needs no mathematical repair or additional theorem.
The separately quarantined prescribed-realization root and remaining consumers
are not restored by this packet; they remain tracked by the rework process.

Return repair: the returned head `c619dbfe719` restored this module on an older
base, and the landing gate rejected its stale base `d92f73d8e`. The current
shared `sheaf-dag` source has the module in quarantine again, as confirmed by
its `coord/rework.tsv` row. Read that current source, reapplied the upstream
model import replacement, and preserved every other byte of the current source.
The sandbox's prior repaired source already agrees with this reconstruction;
no competing source or proof edits are overwritten. This delivery restores the
current quarantined module with its actual import repair, rather than only
rebasing a packet with no Lean change against the current library.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
