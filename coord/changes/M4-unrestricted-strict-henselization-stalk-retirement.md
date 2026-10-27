# AlgebraicGeometry.Etale.unrestricted_strictHenselization_stalk attachment

## Reason

The explicit `coord/retire-items.tsv` entry
`retire:Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk` assigns this
DIFFERENT twin for retirement. The live SHEAF file is already an empty withdrawn
module, and `coord/rework-done.tsv` records its reconciliation on 2026-10-21.
However, node `lem-weil-pbc-unrestricted-strict-henselization-stalk` still attaches
the declaration to that empty module. Repair this dangling Lean attachment.
This is an attachment repair, with zero source holes, rather than a new proof.

The canonical adopted theorem uses `Scheme.strictLocalization` and
`Scheme.strictLocalizationToBase`. The retired theorem used the small
coordinate-ring-colimit model `Scheme.strictHenselizationScheme`. These models
are canonically isomorphic, not definitionally equal. The existing adopted
`Scheme.smallStrictHenselizationColimitIso` and the over-base comparison used by
`LocalAcyclicityClosedFibreStalks` provide explicit transport where needed.
The mathematical unrestricted stalk formula, its qcqs hypotheses and its
canonical restriction assertion are preserved. No theorem or definition is edited.

## Old

The live item source is exactly:

```lean
module

/-! Withdrawn: no declarations remain; use the official WeilConjectures twin. -/
```

The node has `lean.existing = false`,
`lean.module = "Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk"`, and
`lean.declaration = "AlgebraicGeometry.Etale.unrestricted_strictHenselization_stalk"`.
Its recorded signature still refers to the former small model.

## New

Keep the duplicate withdrawn using `deleted.txt`. Attach the node with
`existing = true` to
`WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`, declaration
`AlgebraicGeometry.Etale.unrestricted_strictHenselization_stalk`, and copy its
entire existing signature verbatim into `lean.statement`.
The node statement, statement dependencies, proof, proof dependencies, proof origin,
unit and chapter are unchanged. The independently retained small-model comparison
node and module are unchanged. No source-library declaration, attribute, import,
proof or definition is removed or changed.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
--uses unrestricted_strictHenselization_stalk` reports zero downstream modules
and zero declaration users through the withdrawn module. All live imports of the
unrestricted stalk formula already use the adopted module. No adaptations are needed.
The following rows also reconcile all direct DAG parents with the existing
retirement request; none of their mathematical dependencies is removed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | M4 assignment | Keep already withdrawn; repair its node attachment. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | Already imports the adopted theorem; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks | unclaimed | Already imports the adopted theorem and explicitly transports to the small model; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | unclaimed | Already imports the adopted module; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreUnitStalks | unclaimed | Already imports the adopted module; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | withdrawn | No live declarations; its DAG dependency remains intact. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No use of this empty module; mathematical DAG dependency remains intact. |
| WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula | adopted source | Already imports the adopted theorem; unchanged. |
| WeilConjectures.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | adopted source | Already imports the adopted module; unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyComparisonIso | unclaimed | Retained small-model theorem and its node are preserved verbatim. |

All six direct DAG parents are listed above and retain their dependency.
Other textual citations, including `lem-sc-affine-generic-second` and
`lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion`, are also unchanged.
The unit `sk-thm-br` has no realized attachment to this item; no unit statement
or proof step is bypassed.

## Status

landed 20261024T015224-L-2341644 2026-10-24 (merge of deliver/M4/Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk)
