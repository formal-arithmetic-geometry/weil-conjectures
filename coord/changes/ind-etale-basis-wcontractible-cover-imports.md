# AlgebraicGeometry.Scheme.AffineProEt.exists_weaklyContractible_cover

## Reason

Prove the theorem using the already closed source ring construction and full-site
weak-contractibility theorem, then transport section lifts by the basis restriction
equivalence. Remove every unused import. No declaration signature or definition changes.
The checker requires this record because two unused public imports are removed.

The only direct importer, `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint`,
imports this module for proofs and separately imports both
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` and
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`. It compiles unchanged against the
compiled sandbox version with the pruned imports (2.1 seconds, lcompile.py). All downstream
modules below retain their statements and definitions; none is adapted or delivered.
No target meaning changes or target review is reopened.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
```

## New

These unused public imports are omitted. The file retains its statement dependency:

```lean
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
```

The sole proof import is:

```lean
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
```

All existing signatures and visibility are unchanged. The new helper is private and proved.
The remaining removed proof imports are listed in report.md.

## Users

`tools/downstream.py` listed these 18 transitive importers. The only direct importer was
checked unchanged against the pruned module. Claim holders are from the local snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | E1 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | D2 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | B4 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | D3 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Unchanged signatures and definitions; no adaptation. |
| TargetsCheck | unclaimed | Unchanged signatures and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged signatures and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged signatures and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | Unchanged signatures and definitions; no adaptation. |

## Status

landed 20261015T182203-L-785521 2026-10-15 (merge of deliver/F1/Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover)
