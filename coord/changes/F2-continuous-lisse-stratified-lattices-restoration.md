# continuousLisse_stratified_lattices

## Reason

Restore the assigned quarantined module, preserving its mathematical interface.
The archived source reproduces the recorded global-build error at line 82:
`Unknown constant AlgebraicGeometry.Scheme.exists_etale_stratified_finite`.
Its proof imports the withdrawn Sheaf copy rather than the adopted upstream module
now named by the dependency node's Lean attachment. The restored proof compiles
with the corrected private import.

## Old

The live path `lean/Sheaf/Paper/ContinuousLisseStratifiedLattices.lean` is absent.
Its archived source at `quarantine/Sheaf/Paper/ContinuousLisseStratifiedLattices.lean`
contains the complete public theorem and private system-based proof, with
`import Sheaf.AlgebraicGeometry.EtaleStratifiedFinite`.
The DAG attachment and all mathematical proof dependencies still exist.

## New

Restore the archived module at its original live path, replacing that proof import
with `import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite`.
Preserve the public import, public theorem signature, docstring, and theorem proof.
Remove the unused private helpers `locallyFree_lfp` and `locallyFree_constructible`:
the stratum helper already uses the proved versions from ContinuousLissePullbackSystem.
Remove redundant direct imports of ContinuousLisseStratumDescent,
ContinuousFiniteEtaleLatticeDescent and ContinuousLocallyFreePullback.
Update the item's proof metadata to describe its actual existing system-based proof.
No target, definition, mathematical statement, or public visibility changes.

## Users

`tools/downstream.py` reports an unknown module because the live path is quarantined.
A scan of all live and quarantined Lean sources finds the following two importers,
with the only theorem application in ContinuousConstructibleIntegralStratum.
Both retain the exact archived public signature and public import closure.
No downstream source adaptation is needed or included.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ContinuousLisseStratifiedLattices | F2 (assigned rework) | Restore and repair private proof import; public signature unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | quarantined; not edited | Existing private import resolves when restored; does not apply the theorem. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | quarantined; not edited | Existing theorem call and destructuring retain exactly their original types. |

## Status

landed 20261021T134341-L-889495 2026-10-21 (merge of deliver/F2/Sheaf.Paper.ContinuousLisseStratifiedLattices)
