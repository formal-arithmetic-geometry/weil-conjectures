# Retire the duplicate proper flat Noetherian descent module

## Reason

The queue marks `Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent` for
retirement. The adopted source library already contains the complete theorem
`AlgebraicGeometry.properFlat_single_noetherian_descent` in
`WeilConjectures.AlgebraicGeometry.ProperFlatSingleNoetherianDescent` with the
same public statement. Keeping both modules creates duplicate copies of the
same API and retains an unnecessary long proof in the Sheaf tree.

## Old

The Sheaf module declared `AlgebraicGeometry.properFlat_single_noetherian_descent`
with the node's existing statement and a complete proof of the four-step
Noetherian approximation argument. Its direct live consumer imported
`Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent`.

## New

The Sheaf copy is withdrawn through `deleted.txt`. Its duplicate public and
private imports disappear with the withdrawn copy; the source twin retains the
mathematical dependencies needed by the canonical proof. The existing source module
`WeilConjectures.AlgebraicGeometry.ProperFlatSingleNoetherianDescent` supplies
the same declaration and complete proof. The DAG node
`lem-pc-proper-flat-single-noetherian-descent` is reattached to that source
module; its statement, proof steps and dependency edges are unchanged.

`Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel` changes only its
public import from the withdrawn Sheaf module to the source module. Its theorem
statements and proof bodies are unchanged and compile against the source API.
The quarantined historical `ProperFlatSingleOpenNoetherianComparison` copy is
archival and is not restored or modified by this delivery.

## Users

| module | effect |
| --- | --- |
| `Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent` | withdrawn duplicate |
| `Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel` | import switched to the source twin; proof and interface unchanged |
| `WeilConjectures.AlgebraicGeometry.ProperFlatSingleNoetherianDescent` | retained canonical theorem; source file unchanged |

## Status

landed 20261021T011025-L-2029601 2026-10-21 (merge of deliver/M4/Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent)
The adapted consumer compiles with `lcompile.py`; no source-library file is
changed and no target statement is changed.
