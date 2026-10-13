# AlgebraicGeometry.Etale.tailOpenCohomologyLegDegree_restriction

## Reason

The static interface checker records local attribute commands and scoped elaborator options
as interface changes. This record documents those commands in
`Sheaf.AlgebraicGeometry.EtaleLimitConeRestrictionNaturality`. No theorem type, definition,
visibility, public import, instance or globally exported attribute changes.

The new square calculation must keep inverse-image composition comparisons and cohomology
coefficient maps abstract while matching sheaf morphisms. The local irreducibility of
`upperStarComp` and `Sheaf.H.map` prevents expensive unfolding of these definitions. Removing
these local settings produced a 60-second timeout; with them the complete proof compiled
in 57.1 seconds and the dry-run probe also compiled. No limit was raised and no file split.

## Old

```lean
attribute [local irreducible] upperStar cohomologyMap openCohomologyRestriction
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree

set_option backward.isDefEq.respectTransparency true
```

## New

```lean
attribute [local irreducible] upperStar upperStarComp Sheaf.H.map
  cohomologyMap openCohomologyRestriction
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree

set_option backward.isDefEq.respectTransparency true
```

Each of the two new private helpers is preceded by
`set_option backward.isDefEq.respectTransparency false in`. This option is scoped to the
following declaration. The public theorem keeps the original enclosing true setting.
The second reader replaced its initial simp normalization by explicit unfolding of
`tailOpenCohomologyLegDegree`; the scratch copy with its axiom check compiled in 41.6 seconds.
This avoids unnecessary simplifier normalization while preserving the same proof application. The local attributes end with the namespace/section scope and are
not imported by other modules. The actual definitions of `upperStarComp` and `Sheaf.H.map`
are unchanged, as is the complete public theorem signature.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleLimitConeRestrictionNaturality --uses
 tailOpenCohomologyLegDegree_restriction` reports 279 downstream modules, with two textual
uses of the declaration, including its own declaration. None needs adaptation: the commands
are local and no exported object or signature changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleLimitConeRestrictionNaturality | T2 | Local elaboration only; same public theorem signature, now proved. |
| Sheaf.AlgebraicGeometry.EtaleLimitOpenDifferenceNaturality | unclaimed in this checkout | Unchanged theorem application; no adaptation. |

All other downstream modules import the same public interface. This delivery contains no
forced adaptation, and no target definition or statement changes meaning.

## Status

landed 20261013T224520-L-1475604 2026-10-13 (merge of deliver/T2/Sheaf.AlgebraicGeometry.EtaleLimitConeRestrictionNaturality)
