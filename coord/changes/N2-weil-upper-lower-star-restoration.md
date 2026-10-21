# Restoring Weil pullback and pushforward on bounded constructible objects

## Reason

The assigned row of `coord/rework.tsv` records the module removed after a cluster
restore was reverted. Restore its original missing source interface from
`quarantine/WeilConjectures/WeilObject/BoundedConstructible/UpperLowerStar.lean`.
The rework assignment requires this upstream file byte for byte, including its
one original theorem hole. Its prerequisite interfaces have already been restored.

## Old

The live path
`lean/WeilConjectures/WeilObject/BoundedConstructible/UpperLowerStar.lean`
is absent. The authoritative original source remains at the quarantine path above.
No existing mathematical statement or definition is being weakened or replaced.

## New

The entire archived module is restored verbatim, with its original public imports:

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.WeilObject.BoundedConstructible.Defs
```

This restores `isIso_boundedConstructibleBaseChange_of_isIso`,
`weilUpperStarComparison`, `weilUpperStar`, `weilLowerStarComparison`,
`isIso_weilLowerStarComparison`, `weilLowerStar`, and their object and forgetful
compatibility lemmas in `AlgebraicGeometry.ProEtale.CondensedRing`, with exactly
their archived signatures, bodies, visibility, attributes and docstrings.
The theorem hole is retained without alteration. No target changes meaning.
Byte comparison with quarantine passes; `lcompile.py` compiled the restored module
in 3.8 seconds with exit code 0 and no errors or warnings.

## Users

`tools/downstream.py` with `--allow-missing --uses weilLowerStar` lists the eight
modules below, with zero textual uses of that declaration. An import scan of
`lean/` and `quarantine/` finds one actual direct importer, `TraceFormula.Slop.Basic`.
The restored interface is identical to the one these consumers were written
against. No consumer is edited or delivered, and none requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | N2 | Restore its authoritative archived source. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Direct importer; archived interface restored unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive importer; no change of meaning or adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive importer; no change of meaning or adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive importer; no change of meaning or adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive importer; no change of meaning or adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive importer; no change of meaning or adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive importer; no change of meaning or adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive importer; no change of meaning or adaptation. |

The quarantined `LowerUpperShriek` and the live and archived
`BoundedConstructible.Defs` mention this module in documentation, not imports.
No definition changes relative to the archive; no target semantic review reopens.

## Status

landed 20261021T021020-L-2692232 2026-10-21 (merge of deliver/N2/WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar)
