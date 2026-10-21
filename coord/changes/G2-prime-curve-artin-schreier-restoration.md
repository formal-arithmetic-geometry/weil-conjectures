# Restore PrimeCurveArtinSchreierKernel after the upstream sync

## Reason

The item is listed in `coord/rework.tsv`; its source remains in quarantine.
Two forwarding imports in that archive were retired after the sync. Their
retirement records require migration upon restoration:
`J2-retire-module-abelian-derived-direct-image-comparison.md` and
`retire-abelian-higher-direct-image-presheaf-b3.md`.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
```

Every other byte of the quarantined Lean source is preserved. Both replacements
are the exact upstream providers formerly re-exported by the retired shims, with
the same visibility. The theorem signature, existing hole, proof docstring, DAG
attachment and all mathematical dependencies remain unchanged. No source-library
file is modified.

## Users

The direct archived consumer is
`Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients` (quarantined).
Its declaration use remains valid because the root API is identical. No downstream
module is modified; the cluster's remaining modules are for automatic retry after
the root restoration, as the rework brief requires.

## Status

landed 20261021T101038-L-951 2026-10-21 (merge of deliver/G2/Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel)
