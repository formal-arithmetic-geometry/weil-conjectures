# Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality

## Reason

The assigned row in coord/queue.tsv is a stage-3 `retire` item. The matching
coord/retire-items.tsv row requests replacement by the canonical
WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality module.
D2 already migrated the declarations and their three DAG attachments to that
upstream module in the reviewed canonicalization landed on 2026-10-20.
The current Sheaf file has no declarations and only re-exports that module.
This delivery completes the explicit retirement request against current source.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality

/-! # Raw cohomology pullback and the higher-image comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-naturality).
-/

@[expose] public section
```

## New

Withdraw the Sheaf shim through deleted.txt. The delivery tool replaces its file
with an empty module. The upstream module, all its declarations, definitions,
proofs, signatures, attributes and public imports are preserved verbatim.

The three DAG nodes keep their canonical upstream lean attachments:
- sbc-lem-higher-image-raw-over-comparison;
- sbc-lem-higher-image-raw-over-restriction;
- sbc-lem-higher-image-raw-over-naturality.

Only each lean.note changes to document the completed shim retirement. Their
statements, proof steps, proof dependencies and sources are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed locally | Historical inventory consumer; path already absent, canonical upstream consumer uses the upstream module directly. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | unclaimed locally | Historical inventory consumer; current file re-exports its upstream twin, so no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram | unclaimed locally | Historical inventory consumer; current file re-exports its upstream twin, so no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackComposition | unclaimed locally | Historical inventory consumer; path already absent, canonical upstream consumer uses the upstream module directly. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula | unclaimed locally | Historical inventory consumer; path already absent, canonical upstream consumer uses the upstream module directly. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity | unclaimed locally | Historical inventory consumer; path already absent, canonical upstream consumer uses the upstream module directly. |

Both tools/downstream.py queries (with and without --uses
higherDirectImageRawOverPullback_toSheaf) report zero downstream modules.
Exact-import searches over lean/ and quarantine/ find zero users of the shim.
No consumer adaptation is needed and this delivery writes no consumer modules.

DAG parent checks retain every parent edge to the three nodes. Their canonical
upstream consumers are HigherDirectImageRawAffineImageRep,
HigherDirectImageRawPullbackCompositionFormula, HigherDirectImageRawComplexPresentation,
HigherDirectImageRawDiagram, HigherDirectImageLocalClassVanishing,
HigherDirectImageRawPullbackComposition, HigherDirectImageRawPullbackIdentity,
and HigherDirectImageRawAffineClassVanishing, all under WeilConjectures.AlgebraicGeometry.
The naturality conjunction itself retains both component dependencies.
The unit sk-lem-failure-field has empty realized.statement and realized.steps entries;
no unit step requires this shim path. The mathematics remains on the same route.

There is no matching coord/rework.tsv entry and no current J4 return for this item.
No quarantined source imports the retired path. No quarantined file is removed.
This is retirement of a redundant module path, not withdrawal of its statements.

## Status

landed 20261021T013345-L-2289660 2026-10-21 (merge of deliver/J4/Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality)
