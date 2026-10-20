# AlgebraicGeometry.Scheme.LocallyClosedStratification

## Reason

Retire the duplicate alias and its Sheaf module, as assigned by the human's 2026-10-20
retirement hand-off and coord/retire-items.tsv. The official upstream twin re-exports
WeilConjectures.ConstructibleSheaf.Defs, which already supplies Scheme.Stratification.
Every occurrence of the alias and every direct import of the retired module is adapted.
No adopted-source file changes. There is no change to any target type or definition's meaning.

## Old

```lean
abbrev LocallyClosedStratification (X : Scheme.{w}) := Stratification X
```

Consumers import Sheaf.AlgebraicGeometry.LocallyClosedStratification and may use
LocallyClosedStratification in their declarations and proofs.

## New

The alias is withdrawn; consumers refer directly to AlgebraicGeometry.Scheme.Stratification.
Direct imports become WeilConjectures.AlgebraicGeometry.LocallyClosedStratification,
with the same public/private visibility. No fields or constructors change.
Signatures differ only by delta-reduction of the old abbreviation, including in definitions.

## Users

The complete set of 27 Lean consumers found by searching both library roots for the exact
alias and module name is listed below. This includes indirect consumers of the abbreviation.
The original alias has zero holes; no proof is changed and no hole is added.
The newest landed proof of adic_finite_stratification_pullback and the newest imports
of NormalizedTowerCommonLisseStrata are preserved; they landed during preparation.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback` | M5 | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleAbelianZmodModule` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleNoetherianEtaleModules` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleLocalIsomorphismConstructible` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.BoundedConstructibleTower` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.ContinuousConstructibleModule` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.FiniteFieldSheafScalarExtension` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.FiniteTensorConstructibleCohomology` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.NormalizedTowerCommonLisseStrata` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.ProEtaleConstructibleSheaf` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.ProEtaleFixedModuleConstructible` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.Paper.StratumScalarExtension` | unclaimed | Replace alias by its defining type and/or import upstream twin; definitionally unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteStratificationWidePullback` | unclaimed | Replace alias by its defining type and import upstream twin; definitionally unchanged. |

Twelve DAG lean records are updated to spell their consumer signatures using Stratification.
No node currently attaches to the retired module. The definition node
`def-constructible-stratification` already attaches to the distinct, weaker
`FiniteLocallyClosedStratification`; that attachment is preserved.

The textual downstream scan also reports the following users of consumer declarations.
Their elaborated interfaces are unchanged; they need no source edit.
The scan matches the last name segment, so it also reports `WeilConjectures` for its
existing public import of `WeilConjectures.AlgebraicGeometry.LocallyClosedStratification`.
That import already names the upstream twin and does not refer to the withdrawn alias;
the root module requires no edit, and its adopted-source imports stay verbatim.

| module | group holding it | effect |
|---|---|---|
| `WeilConjectures` | unclaimed | Unaffected: already imports the upstream twin; textual name match only. No source edit. |
| `Sheaf.AlgebraicGeometry.AmplificationConsequences` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleCyclicModuleOfAbelian` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.FiniteLevelAmplification` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroupDevissage` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroupPrimeCases` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineConstructible` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.StalkConstructibilityCriterion` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.CoefficientHeartCommonStratification` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.ConstructibleCoefficientSerre` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.FiniteCoefficientIntrinsicConstructibility` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.FiniteLineTensorConditions` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.FiniteRingCompactSupportProjection` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.FiniteRingConstructibleSheafOrigin` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.FiniteTorsionConstructibility` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.OpenExtensionFiniteTor` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.ProEtaleConstantModuleConstructibility` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.ProEtaleConstructibleExactClosure` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.ProEtaleConstructibleOrigin` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.RestrictionDirectImage` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.SmoothPurityNormalizedTowers` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |
| `Sheaf.Paper.WitnessCompatibility` | unclaimed | Not affected: consumer signatures are definitionally equal after expanding the alias; no adaptation needed. |

## Status

landed 20261020T153004-L-2859933 2026-10-20 (merge of deliver/F9/Sheaf.AlgebraicGeometry.LocallyClosedStratification)
