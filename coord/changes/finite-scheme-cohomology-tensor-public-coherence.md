# AlgebraicGeometry.Scheme.Modules.finiteSchemeCohomologyTensor

## Reason

Restore the quarantined item after upstream sync 5f7b33eac. The rework record reports
that RingedSpace.IsCoherent is only privately imported, although it occurs in the
public theorem type. Make its original source import public. The archived theorem
signature is retained verbatim; its proof is now complete. No definition changes.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.Coherent
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Coherent
```

## Users

The table includes direct consumers in both the current library and quarantine.
All retain the same theorem signature and obtain the needed coherence declaration.
There is no textual call of finiteSchemeCohomologyTensor outside its archived source.
No adaptation is required; no target statement or definition changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme | unclaimed | Same theorem signature; restored public coherence import; no adaptation. |
| Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport | unclaimed | Same theorem signature; restored public coherence import; no adaptation. |

## Status

landed 20261020T145518-L-2405337 2026-10-20 (merge of deliver/J3/Sheaf.AlgebraicGeometry.FiniteSchemeCohomologyTensor)
