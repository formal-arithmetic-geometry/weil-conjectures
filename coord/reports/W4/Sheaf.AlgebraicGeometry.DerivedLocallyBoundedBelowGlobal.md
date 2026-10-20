## What changed

Retired the unused module Sheaf.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal
using deleted.txt. Reattached lem-sc-derived-locally-bounded-below-global to the
existing, proved AlgebraicGeometry.derivedLocallyBoundedBelowGlobal in the upstream
WeilConjectures module of the same suffix. The finite-cover proof and mathematical
statement are unchanged. No source-library file is changed.

Change record: coord/changes/retire-derived-locally-bounded-below-global.md.

## Proved and sorry left

This is the queue's retirement item, with zero original holes. Closed 0 holes, added
0 holes, split off 0 statements. No sorry remains in the withdrawn module. The retained
upstream theorem AlgebraicGeometry.derivedLocallyBoundedBelowGlobal is already proved.

Verification: the original Sheaf module compiles; the retained upstream module and
its existing consumer compile unchanged. The compatibility example applies the
upstream theorem to the original Sheaf signature successfully. Its printed axioms
are exactly propext, Classical.choice and Quot.sound.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal and its duplicate
declaration. Its imports disappear with the withdrawal:
WeilConjectures.AlgebraicGeometry.DerivedCategory,
Mathlib.AlgebraicGeometry.Noetherian,
Mathlib.Algebra.Homology.DerivedCategory.TStructure, and
Mathlib.Topology.Sheaves.Sheaf.

No dependency node is discarded: lem-sc-derived-locally-bounded-below-global stays
attached to the retained upstream theorem. There are zero importers of the Sheaf
module. WeilConjectures.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent already
imports the upstream version and needs no edit. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module containing sorry, but this item has zero
holes and is explicitly queued as retire. The DAG still attached the theorem to the
unused Sheaf copy after its upstream consumer switched to the upstream import. The
older retirement inventory noted a signature difference; it is only the explicit
.{u} on overFunctor in the upstream version, checked against the original signature
by the compatibility example. Retirement removes the duplicate rather than changing
or weakening either mathematical statement.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
