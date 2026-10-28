# AlgebraicGeometry.Scheme.picard_derived_fibre_residue_bridge_core imports
## Reason
The core proof uses the affine naturality and perfect affine representative declarations privately and the geometric compatibility split. Unused public imports were removed to keep the file within the 60-second compile gate.
## Old
The module publicly imported `Sheaf.AlgebraicGeometry.AffineResidueModelNaturality`, `WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative`, `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, and several Mathlib morphism modules.
## New
The module publicly imports only declarations needed by its statement and imports affine naturality and perfect affine representatives privately for the proof.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed | direct importer; compiled by delivery preflight |
## Status
landed 20261028T055709-L-796825 2026-10-28 (merge of deliver/J4/Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore)
