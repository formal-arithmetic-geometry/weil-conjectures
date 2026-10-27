# WeilConjectures.integralOrdinaryDerivedScalar

## Reason

Withdrawn by the reviewer (2026-10-25; first for head `ab78695abb4`, again for the
re-delivery `88ed40c139f`). The delivery proposed turning the
`abbrev integralOrdinaryDerivedScalar` of `Sheaf.Paper.IntegralScalarExtension` into a
`def` with an explicit type and adding two global instances (`CommShift ℤ`,
`IsTriangulated`) for it. The item module `Sheaf.Paper.IntegralOperationsScalarComparisons`
compiles unchanged against the published `abbrev` (F9's landed module `ea304726a2a`;
reviewer compile 10.2 s + 34.6 s, exit 0), and the delivery's own report calls the change
NOT FORCED. A transparency change of a declaration with 36 users that hides instances
behind a `def` boundary is not made without need. `Sheaf.Paper.IntegralScalarExtension`
stays at its published version.

## Old

```lean
noncomputable abbrev integralOrdinaryDerivedScalar :=
  (integralOrdinaryScalar l E L ι Y).mapDerivedCategory
```

## New

Unchanged (no change is made).

## Users

None affected: the declaration is unchanged.

## Status

withdrawn
