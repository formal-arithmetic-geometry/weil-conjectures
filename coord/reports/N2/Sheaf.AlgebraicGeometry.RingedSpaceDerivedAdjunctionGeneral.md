## What changed

Restored Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral as a public
compatibility import of the adopted source module. The source already proves
AlgebraicGeometry.RingedSpace.derivedModulePullback_adjunction; declaring it again
is unnecessary. Reattached lem-pc-ringed-spaces-derived-adjoint-general to that
canonical declaration with its actual signature. Its proof, proof dependencies,
mathematical statement and unit route are retained.

The archived file's missing public changeOfRings/changeOfRingsHom declarations
and missing old K-flat name were reproduced with lcompile.py. The restored module
compiles. A separate probe, importing only the restored Sheaf path, reconstructs
the archived K-flat predicate body and the entire archived signature and supplies
it by the canonical theorem without rewriting or extra hypotheses. The theorem's
axioms are only propext, Classical.choice and Quot.sound.

The consumer check with downstream.py --allow-missing --uses returns zero live
Sheaf importers/users. Searches including quarantined consumers and all DAG
citers are recorded in the change record. No consumer adaptation is needed.
The import-direction check accepts the new public import.

Change record: coord/changes/N2-ringed-space-derived-adjunction-upstream.md.

## Proved and sorry left

This is a quarantine/interface repair with zero original holes, zero holes closed
and zero holes added. No sorry remains in the restored module. No theorem is split
off. The existing source proof of
AlgebraicGeometry.RingedSpace.derivedModulePullback_adjunction is reused; its axiom
check confirms no transitive sorryAx.

## No longer needed

The archived direct imports are replaced by the single canonical public import:
Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage,
Sheaf.Algebra.Homology.KFlatPullback,
Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived,
WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived,
Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute,
Mathlib.CategoryTheory.Functor.Derived.Adjunction,
WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives,
and WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction.
The canonical source supplies the needed interface and imports the proof tools
privately. No mathematical node or dependency module becomes unnecessary. No
source declaration, quarantined archive or module is withdrawn; no deleted.txt.

## Where the brief, the DAG or earlier work was wrong

The assignment is a zero-hole rework item rather than an unproved theorem. The
node still named the quarantined Sheaf declaration although the adopted source
already provides the complete result. Its current K-flat predicate spelling is
IsKFlatTensor, definitionally the archived IsAcyclicTensorKFlat body; the full
archived statement has been checked by direct application. The rework error's
suggested public tensor import alone would leave the missing old predicate and
an unnecessary duplicate declaration. Restoring a canonical public import repairs
the interface while preserving the complete mathematics and dependency route.

Searches performed: Lean Finder for derived tensor pullback/direct-image
adjunction (underived Mathlib results); Loogle for CategoryTheory.Adjunction.derived
(the generic derived theorem); rg across both library roots (the exact adopted
source proof and its three direct uses). No new result or node is introduced.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
