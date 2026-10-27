# AlgebraicGeometry.Etale.strictHenselizationStalkFormula attachment

## Reason

The explicit coord/retire-items.tsv entry
retire:Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula assigns this
DIFFERENT twin for retirement. Its live source is already a withdrawn empty
module, and coord/rework-done.tsv records reconciliation on 2026-10-21.
The node still points to that empty module and records the obsolete small-model
signature. Repair the dangling attachment by reusing the existing adopted theorem.
This is a zero-hole attachment repair, not new proof progress.

The adopted theorem uses Scheme.strictLocalization and
Scheme.strictLocalizationToBase. The former small coordinate-ring-colimit model
used Scheme.strictHenselizationScheme and Scheme.strictHenselizationStructuralMap.
They are canonically isomorphic over the base, not definitionally equal.
Existing consumers which need the small model already transport explicitly,
including Sites.FieldHigherDirectImageStalk and AffineProfiniteFamilySerreCd.
The ordinary formula, its specified restriction map, the bounded-below derived
clause in every integer degree, and all torsion and qcqs hypotheses are preserved.

## Old

The live source is exactly:

```lean
module

/-! Withdrawn: no declarations remain; use the official WeilConjectures twin. -/
```

The node has lean.existing = false,
lean.module = "Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula", and
lean.declaration = "AlgebraicGeometry.Etale.strictHenselizationStalkFormula".
Its old lean.statement uses the former small-model scheme and structural map.

## New

Keep the duplicate withdrawn using deleted.txt. Attach the existing node with
lean.existing = true to
WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula, declaration
AlgebraicGeometry.Etale.strictHenselizationStalkFormula. Copy its complete current
signature verbatim into lean.statement. Only the lean record changes.
No source-library declaration, attribute, signature, public import, definition
or proof is edited. No mathematical node, dependency or unit step is removed.

## Users

The command tools/downstream.py
Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
--uses strictHenselizationStalkFormula reports zero downstream modules and zero
users through the withdrawn module. Source and quarantine searches confirm that
there are no remaining imports of it. No consumer adaptation is necessary.
The following table reconciles the historical retirement inventory and all live
imports of the adopted module; their declarations remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | C2 assignment | Already withdrawn; repair its node attachment. |
| WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula | adopted source | Reuse both proved clauses verbatim. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | Already imports the adopted module. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Already imports the adopted module. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Already imports the adopted module. |
| Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral | unclaimed | Already imports the adopted module. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Already imports the adopted module. |
| Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk | unclaimed | Already uses the adopted formula and explicit small-model transport. |
| Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance | unclaimed | Already imports the adopted module. |
| Sheaf.Paper.AffineProfiniteFamilySerreCd | unclaimed | Already uses the adopted formula and explicit small-model transport. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Already imports the adopted module. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | Already imports the adopted module. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Already imports the adopted module. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Already imports the adopted module. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Already imports the adopted module. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed (historical twin) | No live import of the assigned stub. |

All 21 direct DAG parents keep their mathematical edge unchanged:
lem-wf-boundary-stalk-invariants, lem-trf-geometric-duality-uniform-range,
lem-trf-nearby-specialization-slice, lem-trf-gabber-strict-local-torsion-bound,
lem-trf-oriented-nearby-strict-local-description,
lem-trf-gabber-nearby-cycle-dimension-bound,
lem-trf-nearby-cycle-finiteness-exchange, lem-sfb-affine-profinite-family-serre-cd,
lem-per-truncated-branch-descent, lem-per-perversity-localization-calculus,
lem-per-low-base-open-sheaf-finiteness, lem-per-divisor-purity-strict-local-criterion,
lem-pur-strict-local-constant-unit-criterion,
lem-sc-affine-infinity-boundary-support, lem-kun-affine-direct-image-support-bound,
thm-exc-curve-open-dimension-general, lem-pur-relative-kummer-strict-local-invariance,
lem-pur-relative-kummer-normalized-stalks, lem-sc-field-higher-direct-image-stalk,
lem-pur-a1-direct-image, and lem-sc-affine-polynomial-projection-support.
This includes parents without a current Lean attachment; absence of a live import
is not treated as mathematical irrelevance. Unit sk-prop-h2 has no realized
attachment to this node. Its statement and all its steps stay unchanged.
The small-model BaseChangeGlobalHomology and comparison results remain untouched.

## Status

landed 20261024T184658-L-3103082 2026-10-24 (merge of deliver/C2/Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula)
