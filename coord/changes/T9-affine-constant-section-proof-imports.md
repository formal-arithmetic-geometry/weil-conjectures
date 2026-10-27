# Sheaf.AlgebraicGeometry.AffineConstantSectionZeroDetection

## Reason

The proof uses the canonical continuous-map comparison already occurring in
`constant_pullback_unit_continuousMap`, in coefficient universe `u + 1`.
The separate existential locally constant-section equivalence is unnecessary.
Remove its public import after proving all four clauses with the direct comparison.
The public declarations and their signatures are unchanged.

## Old

```lean
public import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
```

## New

The above import is removed. The existing proof-only import remains:

```lean
import WeilConjectures.AlgebraicGeometry.EtaleConstantSheafPullbackUnitContinuousMap
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineConstantSectionZeroDetection`
reports zero downstream modules. A source search finds no importing modules and
no external users of its two section helpers. There are no consumer adaptations.
The statement-level DAG citation of the locally constant model remains valid.
This changes no definition used by a target, so it does not reopen target statement review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineConstantSectionZeroDetection | T9 | Complete proof; unused public import removed; compiles alone. |

## Status

landed 20261024T191315-L-301320 2026-10-24 (merge of deliver/T9/Sheaf.AlgebraicGeometry.AffineConstantSectionZeroDetection)
