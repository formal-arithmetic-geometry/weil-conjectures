# AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison

## Reason

Restore the quarantined module assigned in coord/rework.tsv after the upstream sync.
Its former public scalar-cohomology provider is now an empty withdrawn module.
The original archive fails to elaborate its public statement: HasPullback and the
ring instances are unavailable, and externalCupCoefficients is imported privately.
The compiler explicitly requests the adopted upstream public provider. The node
for def-sc-field-linear-module-cohomology-operations already names that provider.

## Old

The module is absent from lean/ and preserved in
quarantine/Sheaf/AlgebraicGeometry/ScalarExternalCupModuleComparison.lean.
Its archived provider import is:

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

## New

Restore the entire archive, replacing only that line with:

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The declaration, signature, attributes, docstrings, options, other four imports,
and complete proof body remain verbatim. The Koszul factor (-1)^(p*q) and the
ordinary module cup characterization are preserved. Both proof dependencies stay
in use. No definition, target statement, source-library file, or DAG route changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | G1 | Restore its public provider and unchanged theorem; zero local holes. |
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | unclaimed in local snapshot; quarantined | Its signed theorem application remains valid; no consumer edit. |

The read-only command tools/downstream.py with --allow-missing and
--uses scalarExternalCup_moduleComparison reports zero live downstream modules
and zero live textual users. Searching lean/ and quarantine/ finds the archived
PicardScalarCechExternalCup caller; its DAG parent still needs this node. Hence
this item is restored, not withdrawn. The unit record sk-prop-av-cube is unchanged.

A scratch consumer publicly imports only the restored module, restates its entire
public theorem signature, and applies scalarExternalCup_moduleComparison. The
consumer is checked with lcompile.py together with the repaired module. A fresh
compile of the unchanged current ScalarCupModuleCupCompatibility source is also
used: the previously published compiled theorem references the absent generated
instance FieldLinearModuleCohomologyOperations_monoidalCategory3, whereas its
current source, already restored by K2, compiles correctly. No change to that
source is part of this repair. No other module needs adaptation.

## Status

landed 20261020T154614-L-3136129 2026-10-20 (merge of deliver/G1/Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison)
