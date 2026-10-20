# Retire the duplicate pseudo-coherent RHom theorem

## Reason

The queue marks `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart` for
retirement. Its theorem is already proved by the adopted source module
`WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart`, so the duplicate
Sheaf module is withdrawn and the direct consumer is redirected to the source twin.

## Old

The withdrawn module provided
`AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part` with the theorem statement
recorded in `dag/nodes/sec-picard-framework/lem-sc-rhom-supported-qcoherent-pseudo-part.json`.
Its proof imported the Sheaf component modules and assembled their two conjuncts.

## New

The source twin
`WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart` provides the same
fully proved theorem. Its explicit universe annotations on `overFunctor` and homology are
definitionally identical to the old signature. The DAG node is reattached to that source
module and declaration. The duplicate is withdrawn via `deleted.txt`.

## Users

The unclaimed consumer `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent` changes only
its proof import from `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart` to
`WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart`. Its statement,
proof body, and visibility are unchanged; the adapted file compiles against the source
twin. No other consumer requires adaptation.

## Status

landed 20261020T235609-L-1194334 2026-10-20 (merge of deliver/M3/Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart)
retirement changes only the duplicate module, its direct import, and the DAG attachment.
