# AlgebraicGeometry.Scheme.Modules.isAmple_positive_tensorPow

## Reason

Retirement item in coord/retire-items.tsv, under the human's 2026-10-20 instruction in
coord/changes/retire-sheaf-twins-20261020.md. The upstream twin already proves the same
public theorem. The reported API difference is a private helper,
nonvanishingLocus_app_one, used only within the retired module; no consumer needs it.
The upstream proof uses a local-frame calculation instead. No upstream file changes.

## Old

Module: Sheaf.AlgebraicGeometry.AmplePositiveTensorPower.

```lean
theorem isAmple_positive_tensorPow {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (hM : IsAmple X M) (k : ℕ) (hk : 0 < k) : IsAmple X (M.tensorPow k)
```

## New

Module: WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower.

```lean
theorem isAmple_positive_tensorPow {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (hM : IsAmple X M) (k : ℕ) (hk : 0 < k) : IsAmple X (M.tensorPow k)
```

The Sheaf duplicate is withdrawn through deleted.txt. Each of its three direct consumers
replaces one private proof import with the upstream twin. The repair of returned
head af33c0a1a additionally removes `set_option warn.sorry false` from
GradedImmersionAmpleCriterion: the hole census tokenized the option name as an
unattributed hole. This changes diagnostic suppression only, not a declaration or proof. The node's Lean attachment
points to the upstream file and its proof record describes that existing proof. The two
modules have identical public imports, so their importer-visible dependency interfaces agree.
No definition or public signature changes. No target requires a new statement review.

## Users

The downstream.py scan found eleven downstream modules, including three direct importers.
Only GluedComponentAffineSection currently calls the theorem in a completed proof.
All three adapted direct consumers compiled independently through lcompile.py.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GluedComponentAffineSection | unclaimed | Switch private import; proof compiles unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | unclaimed | Switch private import; existing theorem hole unchanged. |
| Sheaf.TraceFormula.GradedImmersionAmpleCriterion | unclaimed | Switch private import and remove warning suppression; existing named theorem hole unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | not queried; not adapted | Transitive consumer; no interface change. |
| Sheaf.AlgebraicGeometry.CurveProjectiveDenseCompletion | not queried; not adapted | Transitive consumer; no interface change. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | not queried; not adapted | Transitive consumer; no interface change. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | not queried; not adapted | Transitive consumer; no interface change. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | not queried; not adapted | Transitive consumer; no interface change. |
| Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep | not queried; not adapted | Transitive consumer; no interface change. |
| Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram | not queried; not adapted | Transitive consumer; no interface change. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | not queried; not adapted | Transitive consumer; no interface change. |

## Status

landed 20261020T153021-L-2864227 2026-10-20 (merge of deliver/S4/Sheaf.AlgebraicGeometry.AmplePositiveTensorPower)
