# Sheaf.AlgebraicGeometry.LinearIncidenceIrreducible

## Reason

The completed proof opens `MvPolynomial` for polynomial notation and registers its
existing coefficient-extension algebra as a local instance. The delivery gate classifies
these additional commands as an interface change and requires this record. The namespace
opening affects name resolution within this file. The explicitly local instance attribute
expires at the end of the existing public section. The proof-only imports are private.

## Old

The module has `open AlgebraicGeometry`, no `open MvPolynomial`, and no local instance
registration for `MvPolynomial.algebraMvPolynomial`.

## New

The existing `open AlgebraicGeometry` remains, followed by:

```lean
open MvPolynomial
```

Before the localization helpers:

```lean
attribute [local instance] MvPolynomial.algebraMvPolynomial
```

All existing public imports and the exact universe parameters, binders, hypotheses,
conclusion, name and visibility of `linear_incidence_irreducible` are preserved.
The five added helper theorems are private and fully proved. No global instance or
simp attribute is added. No public definition is changed, so no target meaning changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.LinearIncidenceIrreducible
--uses linear_incidence_irreducible` found the following 27 transitive importers.
Only the item itself mentions the theorem name in Lean code; the direct consumer
`Sheaf.AlgebraicGeometry.BertiniIrreducibleMember` currently imports it for its planned proof.
The table includes the item and all importers. Their statements are unaffected because
the public theorem signature is identical and the added instance registration is local.
No consumer adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LinearIncidenceIrreducible | W4 | proof completed; local proof elaboration commands added |
| Sheaf.AlgebraicGeometry.BertiniIrreducibleMember | T5 | no signature or imported elaboration change; no adaptation required |
| Sheaf.Paper.ArithmeticRoots | unclaimed | no signature or imported elaboration change; no adaptation required |
| Sheaf.Paper.WeilOne | unclaimed | no signature or imported elaboration change; no adaptation required |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | no signature or imported elaboration change; no adaptation required |
| TargetsCheck | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Bertini | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.Statement | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.Examples | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | no signature or imported elaboration change; no adaptation required |
| WeilConjectures.ZetaFunction.Weights | unclaimed | no signature or imported elaboration change; no adaptation required |

## Status

landed 20261019T132238-L-1206703 2026-10-19 (merge of deliver/W4/Sheaf.AlgebraicGeometry.LinearIncidenceIrreducible)
