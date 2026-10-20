## What changed

Proved `alpha_vertical` and `alpha_horizontal` by localizing the actual ordinary
natural transformations and applying explicit vertical and horizontal pasting
lemmas for derived-category maps.  The generic localization construction and its factorization lemmas are private
proved helpers in the assigned module. The five remaining holes are unchanged.
The scope-only change is recorded in `coord/changes/DerivedPasting.md`.

## Proved and sorry left

Closed:

- `alpha_vertical`
- `alpha_horizontal`

Remaining:

- `modulePi_components`
- `moduleAlpha_vertical`
- `moduleAlpha_horizontal`
- `alpha_identities`
- `gamma_evaluation`

No new `sorry`s were added.

## No longer needed

None.  The ordinary clopen projection and ordinary pasting declarations remain
needed by the remaining proofs and were not pruned.

## Where the brief, the DAG or earlier work was wrong

The derived localization step in the DAG can be proved uniformly from the
factorization equations for `Localization.liftNatTrans`; it does not require a
separate derived-category theorem for each concrete varying-ring functor.  No
statement was changed.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
