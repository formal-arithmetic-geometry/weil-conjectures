## What changed

Restored Sheaf.Paper.CommonAdicOpenSectionData from its recorded quarantine source.
This is the assigned zero-hole timeout repair. Give the existing Shrink.instField a
module-local priority of 2000, avoiding repeated field-instance search for the small
coefficient models in CommonOpen. Add an explicit functor result type to commonPull,
seal it with irreducible, and prove commonPull_eq by unfolding its unchanged body.
Record that equation in the existing definition node's Lean attachment.

Change record: coord/changes/E4-common-adic-open-pullback-elaboration.md.
No imports, comparison fields, coefficient normalizations or mathematical statements
were removed or weakened. No source-library module was edited.

The original archived source compiles in 18.4 seconds on the current dependencies.
Profiling before and after the local instance priority change reduced cumulative
instance-search time from 6.7 seconds to 1.26 seconds; the latter profiled compile took
15.2 seconds. Development profiling options were removed before final verification.
The final module and the byte-identical archived direct consumer
Sheaf.Paper.CommonAdicCompactificationSectionData both compiled successfully via
lcompile.py --all, with no errors or warnings. The consumer copy was used only for
validation and is not included in the delivery.

## Proved and sorry left

Original item: zero sorries. Final item: zero sorries. Holes closed: zero; holes added:
zero; split off: zero. Newly proved: WeilConjectures.AdicCompactificationSections.commonPull_eq
(blueprint: def-a1-common-adic-open-section-data), the exact implementation equation.
CommonOpen and commonRestrictionHom retain all their original data and formulas.
This is a definition repair, not a claim of a closed pre-existing proof hole.

## No longer needed

None. The original public import, all statement dependencies, the existing Lean
attachment and the quarantined consumer modules are preserved. There is no pruning
or withdrawal, and no new dependency import.

## Where the brief, the DAG or earlier work was wrong

The archived source currently compiles below the recorded 60-second timeout, so that
old failure is not reproducible against the current dependency snapshot. This packet
still makes an actual repair: local field-instance selection is faster, and the
pullback has a typed, sealed implementation with a proved equation API. The existing
node describes comparison data and correctly has no proof holes. Its mathematical
statement and dependency lists need no change.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
