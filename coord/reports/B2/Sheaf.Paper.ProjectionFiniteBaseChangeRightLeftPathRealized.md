## What changed

Replaced the hole in
`WeilConjectures.sixFunctorProjectionFinite_right_left_path_realized`
with an independent right-route transport calculation, without changing its
statement. Private categorical helpers cancel the coefficient comparisons and
use tensor bifunctoriality, exchange conjugation, and naturality of the fixed
projection in both arguments. The existing independent left-route calculation
and fixed-scalar diamond equality then combine the two routes.

The only remaining step is the fixed-scalar presentation identity
`WeilConjectures.finiteProjectionDiamondRight_fixed_coordinates`, stated in the
new module `Sheaf.Paper.FiniteProjectionDiamondRightCoordinates`. It compares the
raw right diamond with three exposed fixed-category factors, for arbitrary
derived inputs. It mentions neither a SixFunctorDatum nor either constructible
route. All coefficient transport and route assembly are proved in the item.

The new imports are private proof imports. Existing public declarations retain
their signatures. No existing shared definition or source-library module changes.
The item's DAG proof record follows the actual argument; the unit route stays.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.sixFunctorProjectionFinite_right_left_path_realized` by a complete
Lean proof from named statements. Added one hole:
`WeilConjectures.finiteProjectionDiamondRight_fixed_coordinates`, node
`lem-sf-finite-projection-diamond-right-fixed-coordinates`. Zero holes remain in
the item module; one remains across the delivery. This is a decomposition, not
net hole reduction. The remaining statement is a strict part of the argument:
it only unfolds the raw diamond into the existing tensor/projection coordinate
API. It does not assert equality of the constructible right and left routes.

The independent transport proof uses no invertibility of projection or exchange,
no finite-Tor assumption on the first input, and no new geometric hypotheses.
The final sandbox compiles cleanly in import order: the new module takes 13.0 s
and the item takes 42.8 s, both below the 60 s limit. The original public theorem
signature was compared verbatim with the shared source.

The remaining coordinate identity is definitional after deleting a mapped
identity, so it also holds for zero inputs, identity squares, and empty schemes.
Its docstring gives all the substitutions and the already proved projection
coordinate equation needed to finish it.

## No longer needed

No original import was removed and no module is withdrawn. No dependency is
claimed as globally pruned. The proof does not import the existing right-route
calculation, route-realization, or transport modules: their current proof chain
depends on this item and cannot be used to prove it. The exploratory raw-expansion
module and shared-definition changes are not included in the delivery.

## Where the brief, the DAG or earlier work was wrong

The existing `ProjectionFiniteBaseChangeRightRouteCalculation` proves its result
from `ProjectionFiniteBaseChangeRightLeftPath`, whose proof depends on this
item. Using it here would be circular. The delivery instead computes the right
route independently and uses the independent left-route calculation and diamond
equality only at the end.

Direct unfolding of the raw diamond repeatedly exceeded the compile limit,
including isolated probes of its defining equation. The categorical transport
and assembly compile independently. This motivated isolating the fixed-category
presentation identity rather than splitting off another copy of the entire
route obligation. No time limit or transparency check was disabled.

## New nodes

`lem-sf-finite-projection-diamond-right-fixed-coordinates` records
`WeilConjectures.finiteProjectionDiamondRight_fixed_coordinates` in
`Sheaf.Paper.FiniteProjectionDiamondRightCoordinates`. It identifies the raw
right diamond with its tensor-comparison, exchange-tensor, and fixed-projection
factors for arbitrary derived inputs. Its only mathematical ingredients are
existing definitions, functoriality of identities, and
`projectionTensorCoordinateComponent_eq`. No change record is needed because
no existing shared statement, definition, or interface changes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteProjectionDiamondRightCoordinates": "021aa695b26b8d72404ee3fbbe0e3ea42ead77e3", "Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPathRealized": "fe9b52ddbc2e21ac2f4c6622ebe2c88e7a71fbfc"}, "results": {"Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath": {"hash": "ff1bd5ff63eca7d417fea07578d2853cc3b2b03f", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T14:21:24+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
