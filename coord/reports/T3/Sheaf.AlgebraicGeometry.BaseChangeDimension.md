## What changed

Completed the queued retirement of Sheaf.AlgebraicGeometry.BaseChangeDimension.
Listed the module in deleted.txt and reattached node base-change-dimension to
AlgebraicGeometry.baseChange_dim in the existing source module
WeilConjectures.AlgebraicGeometry.BaseChangeDimensionExtension.
The original and replacement files are identical from `module` onward, including
all imports, signatures, and proofs. No adopted source module was changed.
Change record: coord/changes/T3-baseChangeDimension-retirement.md.

The former consumer is now WeilConjectures.AlgebraicGeometry.BaseChangeCurve;
it already imports BaseChangeDimensionExtension and applies baseChange_dim.
No current module imports the retired Sheaf copy, as confirmed by downstream.py
and a full source import search. No consumer adaptation is required.

A remote probe imported the replacement and its consumer, proved the exact old
signature from baseChange_dim, and checked the theorem's axioms. It compiled
without warnings in 1.8 seconds; the only axioms are propext, Classical.choice,
and Quot.sound. The scratchpad probe is excluded from the delivery.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero split off.
There are no remaining sorry declarations in the withdrawn module or this packet.
AlgebraicGeometry.baseChange_dim already has a complete proof in the retained
source module. This is duplicate retirement, not a new mathematical proof.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.BaseChangeDimension, including its duplicate
private topologicalKrullDim_eq_iSup_of_affine_openCover helper and public
baseChange_dim declaration. The source implementation retains both.
The withdrawn copy's two public imports (WeilConjectures.AlgebraicGeometry.Curve
and Mathlib.FieldTheory.IsAlgClosed.Basic) and four proof imports
(WeilConjectures.AlgebraicGeometry.Dimension, DimensionAffineOpenCover,
DimensionBaseChange, and BaseChangeConventions) leave with that copy.
Those modules and all existing proof-dependency nodes remain needed by the
retained source proof. No dependency node or unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief names a module with zero holes; the live queue instead
assigns its retirement. The retirement inventory names the similarly titled
WeilConjectures.AlgebraicGeometry.BaseChangeDimension as the proposed twin and
says baseChange_dim is missing. The exact twin actually exists in
WeilConjectures.AlgebraicGeometry.BaseChangeDimensionExtension. Its existing
consumer has already migrated. The DAG attachment still named the unused
Sheaf copy; this packet corrects only that attachment. The statement, proof,
proof dependencies, and unit route are unchanged. No new nodes.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
