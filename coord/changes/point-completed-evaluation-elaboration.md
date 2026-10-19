# PointCompletedEvaluation elaboration boundary

## Reason

The proof of `extension_existsUnique` constructs a functor by choice from a
functorial existence theorem. Later dependent model definitions repeatedly
unfold that choice during elaboration. A local irreducibility attribute keeps
the chosen functor opaque while checking those dependent definitions, reducing
the delivery compile from the 60-second timeout to about 25 seconds. The
attribute is local to this module and does not alter any declaration's type or
value.

## Old

```lean
/-- The ordinary derived dual's bounded-projective chain model, with the recorded differential.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
abbrev dual ...
```

The module had no local irreducibility boundary for `extension`.

## New

```lean
-- The functor's object and map formulas are fixed by the theorem above. Keeping its
-- choice term closed avoids expanding that construction in the dependent model formulas.
attribute [local irreducible] extension
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.PointCompletedEvaluation` | E4 | Dependent local definitions elaborate within the time limit. |

## Status

landed 20261019T231126-L-550471 2026-10-19 (merge of deliver/E4/Sheaf.Paper.PointCompletedEvaluation)
