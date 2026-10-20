# AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model

## Reason

Restore the quarantined item named in `coord/rework.tsv`. Its archived source
contains a complete zero-hole proof, but its original Sheaf derived-pullback
imports conflict with the adopted upstream API. The restored module uses the
adopted `WeilConjectures` imports and retains the theorem signature, definition
interfaces, and DAG attachment. The proof elaboration repairs from the prior
restoration are retained: explicit monomorphism transport, explicit section
universes in open restriction, explicit derived-comparison factor types, and
`rfl` for evaluation of the zero map.

## Old

The quarantined baseline at
`quarantine/Sheaf/AlgebraicGeometry/PerfectUniversalH0BottomModel.lean` used:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology
```

It also used the implicit monomorphism search for the transported kernel map
and the old section-universe inference in the restriction comparison.

## New

The delivered module uses:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedOpenPullbackHomology
```

The mapped kernel inclusion is made explicit with `F.map_mono` and `mono_comp`;
restriction functors and the derived-comparison factors have explicit universe
parameters and types. The evaluation-zero equation is proved by definitional
reduction. No public declaration signature, definition, visibility, or target
statement changes.

## Users

The restored module is consumed by the quarantined
`Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel`, whose theorem
signature remains unchanged. No source-library module is edited and no other
consumer requires adaptation.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel` | B4 | Restored with adopted imports and repaired elaboration. |
| `Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel` | unclaimed/quarantined | Existing import remains valid; no adaptation. |

## Status

landed 20261020T211633-L-3481585 2026-10-20 (merge of deliver/B4/Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel)
