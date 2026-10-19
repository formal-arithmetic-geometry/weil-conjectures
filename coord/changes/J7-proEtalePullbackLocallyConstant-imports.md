# proEtaleConstantModulePullback_locallyConstant imports

## Reason

The unchanged statement uses only the canonical pro-etale inverse-image interface and the
original ringed-module local-constancy definitions. The proof uses the existing coefficient
encoding, the concrete slice-site equivalence, pullback composition and constant-sheaf
comparisons. Remove the unrelated derived-realization reexport and narrow the two other
public imports to the interfaces actually used by the statement. No declaration signature,
universe, visibility, hypothesis, conclusion or definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
```

The proof-only imports are recorded in the delivered module. Its transparency options and
unused-variable linter option are scoped to the theorem. The finite-model hypothesis is
retained verbatim; the proof preserves the exact modules and works without that hypothesis.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExplicitExceptionalPreservation | not adapted | Imports this module only for proofs; the statement and its required public interfaces are unchanged. Already imports ProEtaleConstantRingMap and ProEtaleFixedModuleLocalConstancy separately. |
| Sheaf.Paper.ProEtaleConstructibleExactClosure | not adapted | Imports this module only for proofs; already imports ProEtaleInverseImage and ProEtaleConstantRingMap separately. Its public constructibility interface supplies its statement definitions. |
| Sheaf.Paper.FiniteTorInternalHomAnyField | not adapted | Imports this module only for proofs; its independent public imports supply all statement interfaces. |

These are all three direct importers from tools/downstream.py --direct. The full downstream
scan finds 1479 modules, but none mentions the theorem outside its defining module. All three
edges above are proof-only imports, so no further module receives any reexport from this
module through those edges. No downstream statement or definition changes. No consumer is
edited or adapted, so no forced-adaptation exception is invoked. All three unchanged consumer sources compile against the delivered module: respectively
16.8, 3.5 and 4.0 seconds (the item itself: 9.3 seconds), with no warnings. The delivery import-pruning check additionally
checks downstream source use of lost declarations. No target definition changes.

## Status

landed 20261019T093458-L-2316167 2026-10-19 (merge of deliver/J7/Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant)
