## What changed

Restored Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing from its rework
quarantine archive. Replaced the private import of the retired Sheaf determinant
evaluation with the adopted WeilConjectures theorem and the existing
ExteriorSheafPowerComparison. Transported the two determinant factors through the
single functor and shifts, then composed their tensor comparison with the adopted
evaluation. The final monoidal cancellation proves the exact preserved statement
AlgebraicGeometry.smoothProper_dualizing. No public signature or public import changes.
Updated the item's node to record this transport.

The complete module compiled cleanly through lcompile.py in 3.8 seconds. Checked the
source argument at Stacks duality.tex, lemma-smooth-proper (Tag 0BRT). Local source
search finds the adopted determinant evaluation; LeanFinder finds differential-module
lemmas but no shorter dualizing theorem. Loogle and msearch grep found no exact match.
The existing diagonal-evaluation-plus-determinant route is retained.

Change record: coord/changes/A2-smooth-proper-relative-dualizing-restoration.md.

## Proved and sorry left

AlgebraicGeometry.smoothProper_dualizing is repaired and compiles with its original
statement. This is an assigned zero-hole repair: zero of zero direct sorries closed,
zero added, zero split off, and no direct sorry left in the item or this delivery.
Its existing dependency declarations are used as intended; no claim is made here to
close their transitive holes. The determinant comparison and cancellation are fully
written Lean proofs.

## No longer needed

Removed the obsolete private import
Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation, now a withdrawn empty stub.
Its mathematical node lem-sc-shifted-determinant-dual-evaluation remains needed and
is used via its adopted source-library attachment. No mathematical node or unit step
is pruned. All other original imports serve the statement or diagonal evaluation;
the new private comparison import supplies the conversion between the exterior powers.
No declaration or archive is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The preserved proof called shiftedDeterminant_dual_evaluation from a retired duplicate.
The adopted theorem uses exteriorPower, so changing the import alone would not fit
the existing exteriorSheaf factors. The landed W2 retirement record already documents
the needed comparison transport; this delivery applies it to the actual restored
consumer and its actual diagonal evaluation, without adding a hypothesis or lemma.
The DAG now names the existing comparison node used by that transport. The public
statement, all original mathematical dependencies, and the unit route are unchanged.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
