# AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model

## Reason

Restore the quarantined item named in coord/rework.tsv. Its archived source already has
zero holes, but its old Sheaf derived-pullback imports conflict with the adopted upstream
API. Migrating those imports exposes three proof elaboration failures: an expensive
monomorphism instance search, an incorrectly inferred section universe in the open
restriction comparison, and an unavailable zero-morphism-preservation instance for
section evaluation. Repair all three without changing any public declaration signature,
mathematical definition, or DAG attachment. No source-library file is edited.

## Old

The baseline is quarantine/Sheaf/AlgebraicGeometry/PerfectUniversalH0BottomModel.lean.
Its relevant imports and proof lines are:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology
```

```lean
  have : Mono f' := by dsimp [f']; infer_instance
```

The restriction functors used `SheafOfModules.overMap` and
`SheafOfModules.overFunctor` without an explicit section universe. The negative
Betti-number proof finished its evaluation-zero equation with `exact F.map_zero _ _`.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedOpenPullbackHomology
```

```lean
  have : Mono (F.map f) := F.map_mono f
  have : Mono f' := by
    dsimp only [f']
    exact mono_comp _ _
```

Set the restriction functors' section universe explicitly to `.{u}`, including
`overFunctorMap`. Name the four factors of the derived comparison with explicit
types. The evaluation-zero equation is definitionally true and is proved by `rfl`.
The public theorem signature and all existing docstrings remain verbatim.

## Users

`tools/downstream.py` cannot index the missing quarantined item (it reports
"unknown module(s)"). A text search of both lean/ and quarantine/ finds the sole
consumer below. The item's existing DAG attachment and dependencies are retained.
The module restores the adopted derivedPullback API publicly; the old Sheaf modules
are already empty retired modules in the current tree.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel | U1 (this assignment) | Restored; imports and proof elaboration repaired. |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel | quarantined; no local claim file | Same theorem signature and argument; no consumer adaptation required. |

No other module is edited or withdrawn. No statement or definition changes meaning.

## Status

landed 20261020T174858-L-814708 2026-10-20 (merge of deliver/U1/Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel)
