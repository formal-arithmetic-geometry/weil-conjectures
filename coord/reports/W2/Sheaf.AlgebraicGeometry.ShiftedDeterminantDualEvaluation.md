## What changed

Retire the assigned zero-hole duplicate
Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation in favor of its proved
WeilConjectures twin. deleted.txt withdraws only that active file. Reattach
lem-sc-shifted-determinant-dual-evaluation to the adopted theorem and update its
proof description to match the canonical exteriorPower objects it actually uses.
No upstream file, target statement, definition or mathematical node statement changes.

The source theorem uses exteriorPower, whereas the legacy consumer uses
exteriorSheaf. A complete Lean transport through exteriorSheafPowerIso, the
single functor, both shifts and tensorIso proves the exact old conclusion.
The verification compiled in 3.6 seconds with no warnings and only propext,
Classical.choice and Quot.sound. An independent adopted-theorem axiom check also passed in
2.0 seconds with precisely those axioms. The exact consumer import/call patch and full
verification are recorded in
coord/changes/W2-retire-shifted-determinant-dual-evaluation.md.

The only listed consumer, SmoothProperRelativeDualizing, is quarantined, and
its evaluation dependency and 64 other modules of its chain are quarantined.
Its archive, node attachment and dependencies are preserved. This packet does
not restore that separate rework cluster. There is no active Lean importer.
The complete final consumer cancellation, with only the quarantined evaluation
output supplied as its exact isomorphism hypothesis, compiled in 4.4 seconds
and printed only the permitted axioms. The change record includes the whole
reproducible check; this is not a new lemma or a changed consumer statement.
The mathematical replacement is proved for the full original type, including
independent derived universes. The replacement project source closure has 337
modules, no missing sources, no Sheaf modules and no twin clashes.

## Proved and sorry left

The assigned module started with 0 sorries. Closed 0 of 0; added 0; split off 0;
remaining direct holes 0. AlgebraicGeometry.shiftedDeterminant_dual_evaluation
remains fully proved in the adopted source module. The compatibility verification
has no sorry and has the exact legacy conclusion. This is duplicate retirement,
not a newly proved hole. The four duplicated private derived comparisons leave
with the duplicate; their fully proved source counterparts remain unchanged.

## No longer needed

Withdrawn duplicate: Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation.
Its public imports DerivedTensorStructure, ExteriorSheaf and LocallyFreeRank,
and private imports DeterminantDualEvaluation, ExteriorSheafPowerComparison,
Abelian.Flat.Basic and DerivedCategory.Monoidal.Unit leave with that file.
The adopted proof still uses the ordinary determinant and derived tensor inputs.
ExteriorSheafPowerComparison moves to the legacy consumer boundary and is not a
proof dependency of the adopted theorem; it remains needed for archived consumers.
No additional mathematical node or module is claimed globally unnecessary.
The node and all parent dependencies remain. No blueprint unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a holed theorem; the current queue assigns retirement
of an already proved zero-hole duplicate (retire-items.tsv:1911).
A blind import rewrite fails because the two exterior constructions differ.
The explicit comparison transport fixes that API difference without changing
hypotheses or conclusions. Keeping the old declaration while importing the twin
reproduces the duplicate-name error, so the duplicate must leave.

The retirement row's consumer is quarantined rather than an active source file.
Its absence has not been used to withdraw its mathematics. The archive is intact;
the change record supplies the complete verified conversion required by its
restoration. Full consumer compilation was attempted twice, but the remote
compiler returned no answer after 210 seconds each time; this is not evidence
of a Lean error and is not counted as a successful full-consumer compile.
The general compatibility proof did compile successfully. No launcher or
project tool was edited or bypassed.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
