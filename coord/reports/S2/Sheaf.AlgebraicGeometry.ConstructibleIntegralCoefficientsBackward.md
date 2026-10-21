## What changed

Retired Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward in favor of
WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward, as explicitly
listed in coord/retire-items.tsv. The adopted upstream theorem
AlgebraicGeometry.Scheme.isConstructibleSheaf_integral_backward has exactly the same
signature. Moved the Lean attachment of q1-constructible-integral-coefficients-backward;
all statement and proof dependencies, the proof plan, and audit data are preserved.
No upstream source or target statement changed.

The existing proof retains the same stratum and uses the finite-local abelian comparison,
constant-stalk comparisons, coefficient equivalence, and pullback comparison. The upstream
finiteLocalSets_of_iso uses the newer finite-stalk comparison interface internally.
The old copy compiled successfully. A separate scratch probe applies the upstream theorem
to the exact old public signature and compiled successfully in 4.5 seconds. Both
axiom prints contain only propext, Classical.choice, and Quot.sound.

Change record: coord/changes/retire-constructible-integral-coefficients-backward.md.

## Proved and sorry left

This retirement has zero holes before and zero after: zero holes closed, zero added,
zero split off, and no sorry declarations left in the delivered files. The duplicate's
already proved public theorem is supplied by the existing proved upstream theorem;
this is a retirement, not a new mathematical proof.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward.
Its five public imports and four private imports disappear with the duplicate; no import
of any surviving consumer is removed. No mathematical node or dependency is pruned.
There are zero current Lean importers; downstream.py confirms this. The former Sheaf
parent has already been replaced by WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients,
whose line 95 applies the upstream backward theorem. No quarantined Lean consumer imports
the retired copy. Updating the existing node's Lean attachment preserves all prospective
DAG consumers and the unit route.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with holes, but this is a listed retirement
with zero holes. The retirement register's consumer snapshot still names the already
retired Sheaf parent. The kept-twins snapshot cites prerequisite copies that have since
been retired. Current source, not those snapshots, was used for the consumer check.
Searches through msearch.py (LeanFinder, Loogle, grep) and direct library rg were run;
direct source inspection found the exact upstream theorem, so no new lemma is needed.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
