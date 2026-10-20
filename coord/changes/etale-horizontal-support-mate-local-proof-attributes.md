# AlgebraicGeometry.Etale.etaleHorizontalSupportMate

## Reason

Repair of return bf6cc6581: remove the unnecessary file-level warning-suppression
option, which the hole ledger classified as an unattributed hole. This changes only
warning output; no declaration, definition, attribute or public import is changed by
this repair.

The proof uses local irreducibility attributes to keep categorical constructions opaque
while elaborating mate identities. The static interface detector records these commands,
although each attribute is explicitly local and is not exported to importers. This record
also covers the new public theorem in `EtaleHorizontalSupportTower`. All existing public
imports, all three existing definition bodies, and the item theorem signature are byte-for-byte
unchanged. No target meaning changes and no consumer adaptation is required.

## Old

The item had the file-level option `set_option warn.sorry false`.

There were no local irreducibility attribute commands in the item. The new tower theorem
and module did not exist. The existing item signature and definitions are preserved verbatim.

## New

The warning-suppression option is removed; default warning behavior applies.

The added commands in the item, verbatim:

```lean
attribute [local irreducible] canonicalEtaleCompactSupportComparison

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

attribute [local irreducible] derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction

attribute [local irreducible] rightDerivedLowerShriekIso
  unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr
  mapDerivedUpperStarLowerStarAdjunction
```

The new public statement is
`AlgebraicGeometry.Etale.etaleHorizontalSupport_tower`; its full signature is verbatim in
`dag/nodes/sec-smooth-purity/lem-pur-etale-horizontal-support-tower.json`, field `lean.statement`,
and in `lean/Sheaf/AlgebraicGeometry/EtaleHorizontalSupportTower.lean`. It is a separate
canonical graph composition normalization before counits, not a replacement signature for
the item. Its only hole is a named theorem body; no definition has been changed.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate --uses
etaleHorizontalSupportMate` reports the following import closure and only a self-occurrence
of the declaration name. Every downstream module retains exactly the same existing API.
The direct parent proofs remain unfinished; their DAG dependence is retained.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate` | F9 | Private proof helpers and local attributes only; existing interface preserved |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No edit; public signatures and definitions identical; local attributes are not exported |

## Status

landed 20261020T221148-L-4151252 2026-10-20 (merge of deliver/F9/Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate)
