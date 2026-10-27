# AlgebraicGeometry.Scheme.adicResidue_koszul_coefficient_cone_comparison

## Reason

The assigned theorem takes a normalized coefficient augmentation as input and
uses none of the augmentation-existence theorem or its proof dependencies.
Its public import of the augmentation module unnecessarily loads the negative
Koszul duality and low-degree proof modules during this finite comparison.
The quotient-tower module supplies every coefficient notion used in the
unchanged statement. Remove the unnecessary re-export while keeping its
required public dependency directly.

## Old

```lean
public import Sheaf.Paper.AdicResidueKoszulCoefficientAugmentation
```

## New

```lean
public import Sheaf.Paper.AdicResidueQuotientTensorTower
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicResidueKoszulTensorConeProZero | unclaimed in the current claim records | Sole direct importer; already publicly imports AdicResidueKoszulCoefficientAugmentation independently, so its declarations and exports are preserved. Its original source failed the timing check; the separate M4-adic-residue-cone-consumer-timing.md record documents its proof-only timing repair. |

The sole use elsewhere of the augmentation-existence theorem is in
AdicResidueStrictKoszulAugmentation, which obtains its export through that
independent public import in AdicResidueKoszulTensorConeProZero. No consumer interface adaptation or target/definition/signature change is
required. The proof-only timing repair is documented separately.

## Status

landed 20261026T135627-L-4051345 2026-10-26 (merge of deliver/M4/Sheaf.Paper.AdicResidueKoszulCoefficientConeComparison)
