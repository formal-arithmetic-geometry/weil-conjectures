# finite comparison localizing proof route

## Reason

The restored item needs a proved ordinary full-faithfulness interface and a separate
finite generator correspondence to construct the localizing equivalence. The proof
also uses the `ZeroObject` scoped notation and the internal module equivalence imports.
These additions change the declarations and imports visible to downstream modules, so
this record accompanies the delivery.

## Old

`Sheaf.Paper.FiniteComparisonLocalizing` exposed the archived coefficient and closure
definitions, with `finiteComparisonRealization_exact` and
`finiteComparisonLocalizing` left as `sorry`; it did not import
`Sheaf.Paper.FiniteComparisonFaithful` or the internal module encoding modules.

## New

The item proves `finiteComparisonRealization_exact` and
`finiteComparisonLocalizing`, imports the internal module encoding and closure support,
and exposes the intermediate theorem
`AlgebraicGeometry.ProEtale.finiteComparisonGenerators_identification`.
The new module `Sheaf.Paper.FiniteComparisonFaithful` exposes the proved theorem
`AlgebraicGeometry.ProEtale.finiteComparisonOrdinary_fullyFaithful`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.FiniteComparisonLocalizing` | C3 | Defines and uses the two proof interfaces |
| downstream finite comparison importers | unclaimed | See the same declarations and their unchanged intended types |

## Status

landed 20261021T012352-L-2180691 2026-10-21 (merge of deliver/C3/Sheaf.Paper.FiniteComparisonLocalizing)
