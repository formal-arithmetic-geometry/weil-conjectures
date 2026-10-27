# AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace

## Reason

The repaired definition needs a named, strictly smaller statement for the geometric
finite-to-adic-to-condensed construction.  This public theorem is added under
`Sheaf.SmoothPurity.TraceExistence`; it records the unresolved construction as a
separate stage-3 item and does not alter any existing source declaration.

## Old

No declaration with this name existed in the source library.

## New

`Sheaf.SmoothPurity.TraceExistence` adds the theorem
`AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace`.  Its signature is
recorded verbatim in node
`lem-route-smooth-trace-representing-unique`; its proof is the finite smooth-purity
Hom pairing, normalized integral Tate-tower reconstruction, condensed scalar
realization, and uniqueness from the adjunction Hom equivalence.

## Users

| Module | Group holding it | Effect |
| --- | --- | --- |
| WeilConjectures.SmoothPurity.Defs | A2 | Uses the unique witness to define `smoothTrace`. |

## Status

landed 20261027T205753-L-1613179 2026-10-27 (merge of deliver/B2/WeilConjectures.SmoothPurity.Defs)
