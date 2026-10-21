# finiteFieldAbLocallyBijective

## Reason

The existing `WeilConjectures.integralCoefficientAbLocallyBijective` instance has
coefficient universe `max r (u + 1)`. Searching for the fixed module universe
`u + 1` leaves `r` undetermined. A specialization at explicit universe arguments
avoids this elaboration failure in the proof of finite stratified generation.
The first delivery preflight requested this record for the original local
instance. The repaired packet also marks the declaration `private`, making both
its name visibility and its instance scope explicit.

## Old

There was no specialization named `finiteFieldAbLocallyBijective` in this module.
The generic criterion and all existing declaration signatures are unchanged.

## New

```lean
private local instance finiteFieldAbLocallyBijective (X : AlgebraicGeometry.Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X
```

The other added instances, `FiniteStratifiedConstruction.built_replete` and
`FiniteStratifiedConstruction.built_triangulated`, are private proved closure
instances on the private finite-prefix predicate. They cannot alter the meaning
of any existing object property or theorem statement. All new definitions are
private proof bookkeeping with actual data and no holes; all public imports and
existing public signatures remain verbatim.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.FiniteFieldStratifiedGeneration` | U3 | Uses the private local specialization and private finite-prefix closure instances in its proof. |

`tools/downstream.py Sheaf.Paper.FiniteFieldStratifiedGeneration --uses
finiteFieldAbLocallyBijective` reports zero downstream modules and zero users of
this new name. A direct import search also reports no current Lean importers.
Unfinished DAG parents retain the unchanged theorem interface and dependencies;
no parent is withdrawn. No consumer adaptation is required.

## Status

landed 20261021T120731-L-3939761 2026-10-21 (merge of deliver/U3/Sheaf.Paper.FiniteFieldStratifiedGeneration)
