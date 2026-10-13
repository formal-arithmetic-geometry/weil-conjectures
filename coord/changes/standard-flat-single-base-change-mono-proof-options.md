# AlgebraicGeometry.standard_flat_single_baseChange_homology_mono

## Reason

The proof requires elaboration options. The delivery checker classifies added
`set_option` commands as environment changes, so this record identifies them.
No mathematical interface changes.

## Old

The repository has `set_option autoImplicit false`, no transparency overrides,
and the unchanged theorem signature followed by `:= by sorry`.

## New

The two added module-local commands are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The theorem has the declaration-local command:

```lean
set_option maxHeartbeats 400000 in
```

The theorem body supplies the stalk and canonical-map reduction. These options
control elaboration in this module; they do not change theorem signatures,
definitions, public imports, kernel checking, or the 60-second compile limit.
The transparency commands apply to the private helpers as well as the theorem;
only the heartbeat command is scoped to the theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono | M2 | proof elaboration only |

## Status

landed 20261013T201801-L-3973939 2026-10-13 (merge of deliver/M2/Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono)
