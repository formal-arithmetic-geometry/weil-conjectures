# AlgebraicGeometry.Etale.properOpenComparison_coefficient_refinement

## Reason

The completed proof uses only `ProperOpenComparison`, the scalar mate interface,
Noetherian schemes, derived plus compatibility, open lower-shriek definitions,
and proof-local categorical APIs. The old public imports
`Sheaf.AlgebraicGeometry.OpenSectionClopen` and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` are therefore no
longer part of this module's public interface. Removing them prunes unused
transitive work while preserving every declaration signature and theorem
statement. The proof-only imports were also replaced by the smaller imports
actually used by the delivered proof.

## Old

```lean
public import Sheaf.AlgebraicGeometry.OpenSectionClopen
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
```

## New

Those two public imports are removed. The module retains its other public
imports and imports `Sheaf.Paper.ScalarPullbackComposition` and
`Sheaf.AlgebraicGeometry.ProperOpenIdentificationNormalization` privately for
its proof.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SixFunctors.CompactCoefficientComposition` | U6 | public-import closure is reduced; no declaration signature changes |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | K8 | public-import closure is reduced; no declaration signature changes |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | U5 | public-import closure is reduced; no declaration signature changes |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | public-import closure is reduced; no declaration signature changes |
| `Sheaf.Paper.RefinementCoefficientMate` | unclaimed | public-import closure is reduced; no declaration signature changes |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | V5 | public-import closure is reduced; no declaration signature changes |

All six original direct importer modules compile against the delivered parent
overlay unchanged (5.8–25.7 seconds). No definition or declaration signature is
changed, so downstream mathematical statements and target meanings are unchanged.
The two added elaboration options affect only proof elaboration, not declaration
visibility or data.

## Status

landed 20261020T051447-L-1688209 2026-10-20 (merge of deliver/K3/Sheaf.Paper.ProperOpenCoefficientRefinement)
