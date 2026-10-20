## What changed

Retired Sheaf.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection in favor
of WeilConjectures.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection.
Listed the duplicate in deleted.txt and redirected the lean attachment of
lem-sc-affine-principal-cover-quasi-iso-detection to the existing official theorem.
The public signature is verbatim identical. The only code differences apart
from copyright are explicit universe annotations in private helper proofs.
No source-library file, consumer, mathematical statement, or target changed.

Change record: coord/changes/retire-affine-principal-cover-quasi-iso-detection-V2.md.

## Proved and sorry left

This is the queue's retirement task, with zero initial holes. Closed 0 of 0
sorries; added 0; split off 0; none remain in the withdrawn module.
AlgebraicGeometry.Scheme.affine_principal_cover_quasiIso_detection remains fully
proved in the official twin. The duplicate compiled unchanged via lcompile.py
in 36.0 seconds before withdrawal. An unchanged scratch copy of the current
official consumer WeilConjectures.AlgebraicGeometry.AffineOpenLocalizedModel
compiled through lcompile.py in 18.2 seconds. Its #print axioms probe for the
retained theorem returned exactly propext, Classical.choice, and Quot.sound.
The delivery dry run checks that no remaining module imports the withdrawn copy.

## No longer needed

The entire duplicate module Sheaf.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection
is withdrawn. No module currently imports it, so no consumer import needs an edit.
The former Sheaf.AlgebraicGeometry.AffineOpenLocalizedModel consumer listed in the
retirement inventory is already absent; its official twin already uses the
official detection module. No proof dependency or DAG node is discarded:
lem-sc-affine-principal-cover-quasi-iso-detection remains attached to its official
implementation. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The general proof brief describes a holed or repaired module, but the queue
specifically classifies this item as retire. Both implementations have zero
holes. The inventory's former Sheaf consumer has already been retired, so its
consumer count is stale. The DAG still pointed at the duplicate, which this
delivery repairs. The DIFFERENT classification concerns a private helper's
explicit universe annotations; the public theorem signature is identical.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
