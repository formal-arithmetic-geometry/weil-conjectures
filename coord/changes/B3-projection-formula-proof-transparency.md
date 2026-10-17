# Exceptional projection formula: local proof transparency

## Reason

The delivery replaces the original exceptional-projection instance proof with a
compactification argument. The static checker requests this record for local
reducibility commands before the instance. No existing signature, visibility,
definition body or instance registration changes.

## Old

There were no local reducibility attributes immediately before
`isIso_boundedConstructibleExceptionalProjectionMorphism`. Its type was
`IsIso (boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B)` and its body
was `sorry`.

## New

Immediately before the unchanged instance declaration:

```lean
attribute [local irreducible] CategoryTheory.Adjunction.projectionMorphism
  derivedUpperStarLowerStarAdjunction
```

These attributes prevent unnecessary expansion of the adjunction and its projection
component while composing the proper, open and pullback-comparison factors. Both
are local to this module. The additional import
`Sheaf.PoincareDuality.ProperProjectionFormulaBounded` is a proof-only import.
The new proper-factor theorem has its own new DAG node and module. It adds one hole
while the exceptional-projection instance loses one: this is a decomposition.

## Users

`python3 tools/downstream.py WeilConjectures.PoincareDuality.ProjectionFormula
--uses isIso_boundedConstructibleExceptionalProjectionMorphism` reports four
transitive downstream modules: `TargetsCheck`, `WeilConjectures`,
`WeilConjectures.PoincareDuality.Poincare`, and
`WeilConjectures.PoincareDuality.Verdier`. The only textual uses of the instance
name are in its own module. The original instance type is unchanged, and the
local reducibility commands do not propagate to importers. No consumer needs
adaptation, no consumer statement changes meaning, and no target statement
review is reopened. No other group's module is changed.

Both delivered modules compiled together through `lcompile.py --all`: the new
helper in 4.9 seconds, the original module in 57.6 seconds. The import-direction
checker confirms there is no cycle.

## Status

landed 20261017T234739-L-903832 2026-10-17 (merge of deliver/B3/WeilConjectures.PoincareDuality.ProjectionFormula)
