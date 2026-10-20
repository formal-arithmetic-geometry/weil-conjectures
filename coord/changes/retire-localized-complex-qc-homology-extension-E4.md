# AlgebraicGeometry.localized_complex_qc_homology_extension

## Reason

The retirement inventory assigns this Sheaf module to the adopted source twin
`WeilConjectures.AlgebraicGeometry.LocalizedComplexQCHomologyExtension`. Both modules
contain the same public theorem and both are compiled without holes. The Sheaf copy is
therefore a duplicate compatibility module. Its only current library consumer is
`Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology`, which can import the source
module directly while preserving the theorem invocation and all public interfaces.

## Old

The item module `Sheaf.AlgebraicGeometry.LocalizedComplexQCHomologyExtension` declares
`AlgebraicGeometry.localized_complex_qc_homology_extension` with the statement recorded in
`dag/nodes/sec-picard-framework/lem-sc-localized-complex-qc-homology-extension.json`.
The consumer imports it with:

```lean
import Sheaf.AlgebraicGeometry.LocalizedComplexQCHomologyExtension
```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/LocalizedComplexQCHomologyExtension.lean` through
`deleted.txt`. The DAG node's Lean attachment points to the existing source declaration
`WeilConjectures.AlgebraicGeometry.localized_complex_qc_homology_extension`, whose type is
unchanged. The sole consumer imports:

```lean
import WeilConjectures.AlgebraicGeometry.LocalizedComplexQCHomologyExtension
```

No theorem signature, public import, proof body, target statement, or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology | unclaimed | Replace one private proof import by the adopted source twin; theorem use and public API are unchanged. |
| Sheaf.AlgebraicGeometry.LocalizedComplexQCHomologyExtension | E4 | Duplicate module withdrawn; its theorem is supplied by the source twin. |

The source scan finds no other importers of the withdrawn Sheaf path.

## Status

landed 20261020T144244-L-2258868 2026-10-20 (merge of deliver/E4/Sheaf.AlgebraicGeometry.LocalizedComplexQCHomologyExtension)
