# Rework of TensorModelRestrictionComparisons after upstream synchronization

## Reason

The upstream synchronization quarantined this module because its public import
of `Sheaf.AlgebraicGeometry.DerivedTensorAugmentation` conflicted with the same
source declaration brought in by
`WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom`:

`environment already contains AlgebraicGeometry.Scheme.IsDerivedTensorAugmentation from Sheaf.AlgebraicGeometry.DerivedTensorAugmentation`

## Old

The quarantined pre-sync module publicly imported
`Sheaf.AlgebraicGeometry.DerivedTensorAugmentation` and privately imported the
source canonical tensor-Hom module. Its theorem and private proof were the
versions delivered before the 2026-10-20 upstream synchronization.

## New

The repaired module removes the conflicting Sheaf DerivedTensorAugmentation
public import and adds `public import Sheaf.Algebra.Homology.KFlat`, which
exposes `CochainComplex.IsAcyclicTensorKFlat` used in the unchanged theorem
statement. The declaration signatures and proof body are unchanged.

## Users

The module's importers are the quarantined modules
`Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction` and
`Sheaf.AlgebraicGeometry.TensorRoofTransposition`. They continue to use the
same theorem; no importer source changes are required. The import change only
removes the duplicate declaration and preserves the K-flat predicate's public
availability.

## Status

landed 20261020T152951-L-2856384 2026-10-20 (merge of deliver/D3/Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons)
compile passes; delivery preflight is the remaining verification.
