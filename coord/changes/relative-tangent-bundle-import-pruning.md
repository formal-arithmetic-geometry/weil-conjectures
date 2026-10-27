# AlgebraicGeometry.RelativeTangentBundle

## Reason

Proving both existing theorems uses only the general structure-algebra equivalence and
augmentation API, the affine symmetric-algebra comparison, and relative differentials.
CoherentFiniteType is unused. The Core and AffineMorphismRelativeSpec imports are redundant:
VectorBundleZeroSection publicly imports both. The local irreducibility attribute keeps
the affine-chart proof from unfolding the chosen quasi-inverse; it has no exported effect.
No public declaration signature or definition changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
```

No local irreducibility attribute preceded affineChart_spec.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
```

Before affineChart_spec, locally only:

```lean
attribute [local irreducible] VectorBundleZeroSection.antiEquivalence
```

All existing public declaration signatures and definitions remain verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeTangentBundle | M5 | Both proofs filled; no signature changes. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed in local claim mirror; quarantined | Uses scheme, projection, zeroSection, algebraIso, and symmetric generators; all preserved. No occurrence of IsQuasiCoherentFiniteType. No adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed in local claim mirror; quarantined | RelativeTangentBundle import only; no use of IsQuasiCoherentFiniteType. No adaptation. |

The source-only downstream check originally listed these two consumers. During delivery,
the shared source refresh quarantined both at their preserved quarantine/Sheaf/Paper paths;
the current downstream command lists zero active consumers. Both archived consumers have
been rechecked and retained. Neither archive is changed or withdrawn by this delivery.
Core and relative-spectrum APIs remain publicly available through VectorBundleZeroSection.
The local irreducibility attribute cannot affect importers. No target statement or its
underlying definitions changes, so no target statement review is reopened.

## Status

landed 20261023T103112-L-3052028 2026-10-23 (merge of deliver/M5/Sheaf.AlgebraicGeometry.RelativeTangentBundle)
