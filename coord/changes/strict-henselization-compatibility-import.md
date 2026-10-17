# Public visibility of StrictHenselizationLocal import

## Reason

The theorem `AlgebraicGeometry.strictHenselizationLocalStructure` uses the upstream
strict-henselization instances only in its proof. The type in its public signature is
provided by the public Henselian import. Make the upstream local-structure import
private so this compatibility module does not re-export an implementation dependency.
The theorem statement, definitions, and all downstream declarations remain unchanged.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
```

## Users

The seven direct importers retain their existing imports, signatures, and proofs. They
use the compatibility theorem or other declarations from this module, and do not rely
on the upstream module being re-exported by it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | Existing interface and proof unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Existing interface and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Existing interface and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | Existing interface and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | Existing interface and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Existing interface and proof unchanged. |
| Sheaf.Paper.StrictHenselizationFunctoriality | unclaimed | Existing interface and proof unchanged. |

## Status

landed 20261017T003418-L-3313882 2026-10-17 (merge of deliver/E2/Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility)
