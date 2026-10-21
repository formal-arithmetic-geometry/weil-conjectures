# AlgebraicGeometry.single_open_tensor_coefficient_coherence

## Reason

Restore the module assigned in `coord/rework.tsv` from its quarantine archive.
The archive is already fully proved, but Lean rejects its local reducibility
command because upstream now declares `derivedPullback` with `irreducible_def`.
Remove the redundant attribute from that command. A proof-only import also
names the selected counit through the existing `perfectHomTensorCounit`
abbreviation, preserving its exact choice. Keep the original public theorem,
public imports, docstrings, and DAG attachment intact.

## Old

The module is absent from `lean/`. Its archived proof contains:

```lean
attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.tensorPullbackObj
```

The original compile fails at this command because `derivedPullback` is already
irreducible. The archive contains zero holes.

## New

The restored module uses:

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.tensorPullbackObj
```

The public theorem's signature and proof are verbatim. Add the proof-only import
`WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit` and replace the literal
selected counit in the private `tensor_single_normalize` statement and the
`tensor_single_naturality` proof:

```lean
(Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
```

by its existing definitionally equal name:

```lean
perfectHomTensorCounit f
```

All other private proof code and the remaining local attributes and options are
retained. No exported definition, theorem signature, or target meaning changes.
The final source compiles in 37.3 seconds and its exact axiom probe completes in
40.7 seconds under the unchanged 60-second limit, with no forbidden axiom or
hidden hole.

## Users

`tools/downstream.py --allow-missing --uses` finds no current Lean importer:
the item is quarantined. Searching the archive finds the direct consumer below;
its call uses the unchanged theorem and needs no source adaptation. Its DAG
parent remains attached and no module is withdrawn.

The unchanged archived consumer compiled against the repaired item in the same
sandbox: item 39.0 seconds, consumer 28.7 seconds, both clean. Its unchanged
`StandardSingleBaseChangeMap` prerequisite compiled in 2.5 seconds. The current
upstream `DerivedBaseChangeSourceIso` source compiled in 28.7 seconds to replace
an older published artifact for the check. None of these test copies is changed
or delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence | E3 | Restored; obsolete local attribute removed. |
| Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow | unclaimed | Original theorem interface retained; no adaptation. |

## Status

landed 20261021T002932-L-1580059 2026-10-21 (merge of deliver/E3/Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence)
