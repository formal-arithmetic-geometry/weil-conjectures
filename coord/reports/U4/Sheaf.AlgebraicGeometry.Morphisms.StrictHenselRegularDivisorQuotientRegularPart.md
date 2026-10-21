## What changed

Completed the zero-hole retirement listed in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart`.
Withdraw the duplicate using `deleted.txt` and attach its mathematical node to the
proved upstream twin. Adapt its two direct consumers, DomainPart and Regular,
to import that twin and explicitly transport regularity from the full
strict-henselization colimit to their original small-colimit quotient.

The private `comparison_base` proof moves from the retired item into both consumers.
The forward ring comparison carries the structural map and nonunit hypothesis to
the upstream theorem. Its inverse induces `Ideal.quotientEquiv`; Mathlib
`IsRegularRing.of_ringEquiv` supplies regularity of the actual small quotient.
Both consumer public theorem signatures, visibility and existing docstrings are
unchanged. Replace their public structural-map wrapper import with its upstream
owner, which provides the same definitions and avoids the duplicate equation name.
The remaining local-domain argument and conjunction assembly are preserved.

Updated the item's Lean attachment and proof, and the two consumer nodes' proofs.
All mathematical dependency edges and the unit route remain intact. No source-library
file, target, definition, quarantined file or new node is changed.
Change record: `coord/changes/U4-retire-strict-hensel-regular-divisor-quotient-regular-part.md`.

## Proved and sorry left

Starting item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No `sorry` remains in either delivered Lean file. The retired theorem
`AlgebraicGeometry.Scheme.strictHenselizationRing_regular_divisor_quotient_part`
already has a complete proof in the retained upstream module. The adapted
`AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_domain_part`
and `AlgebraicGeometry.Scheme.strictHenselizationRing_regular_divisor_quotient`
are completely proved, along with their private comparison helpers.

All eleven downstream modules compiled as individual files against the adapted
consumers and the compiled withdrawn stub, without warnings (2.1–10.2 seconds
per file). The unchanged verification copies were removed from the delivery.
Against the stub, the original DomainPart fails at line 31 with an unknown
`strictHenselizationRing_regular_divisor_quotient_part`; the original Regular
fails at line 26 with the same error. The adapted consumers compile in 3.7 and
3.8 seconds. The delivery tool runs the final compilation and axiom probes.

## No longer needed

Pruned module:
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart`.
Both direct consumers remove that private import and use its upstream twin.
Their public `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` import is
replaced by `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`;
this delivery does not withdraw the separately assigned structural-map wrapper.

The retired item's private auxiliary import is supplied by the upstream regularity
proof. Its node `lem-sbc-strict-hensel-regular-divisor-quotient-regular-part-aux`
remains needed, and the regularity node remains needed by both parent proofs.
The colimit-comparison argument is retained in both consumers. No other mathematical
node or module is claimed pruned, and no blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief suggests a hole, but the current queue marks the item
`retire` and its live module has zero holes. The concrete assignment is retirement
of a proved duplicate. Its twin has the full-colimit statement; the small-colimit
consumer statements require the explicit transport now written in Lean. An import
swap alone would not repair them.

A parsed DAG scan finds exactly the same two actual parents through dependency
fields and proof-step uses; both are updated. Other item-node mentions are provenance.
No quarantined Lean file imports the item or uses its theorem. The item node keeps
its mathematical meaning and auxiliary dependency; the new Lean attachment records
the full-colimit presentation and explains the equivalence implemented by both
consumers. No statement or unit-route error was found. The transport imposes no
extra assumptions on the divisor and covers `f = 0` and dimension-zero rings.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
