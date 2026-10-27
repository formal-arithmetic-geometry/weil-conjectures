## What changed

Proved `AlgebraicGeometry.Scheme.stratumReduction_evaluation` from the existing
`stratumReduction_evaluation_on_KFlat` declaration. The two sides are components
of natural transformations. Choose a flat-term K-flat resolution of an object
representing the arbitrary derived object, turn its quasi-isomorphism into an
isomorphism in the derived category, and transport the representative identity
by naturality and cancellation of that isomorphism. The flatness hypothesis is
transported through `siteSheafTensorRightIso`.

This follows the localization step already described in the declaration's proof
and the existing DAG route. No statement, definition, import, or DAG attachment
changes, and no new theorem or node is introduced.

Validation: the item compiled through `lcompile.py` in 53.2 seconds (exit 0).

## Proved and sorry left

The item initially contained two holes. Closed one:

- `AlgebraicGeometry.Scheme.stratumReduction_evaluation`.

One existing hole remains, unchanged:

- `AlgebraicGeometry.Scheme.stratumReduction_evaluation_on_KFlat` (node
  `lem-weil-pbc-stratum-completion-unit-restriction-evaluation-kflat`). This is
  the tensor-balancing and counit-normalization identity on a flat-term K-flat
  representative. Its source and proof in words remain in its docstring and node.

Added holes: zero. Split-off statements: zero. The proved arbitrary-object
identity uses the remaining representative identity, so the complete module is
not yet free of proof holes.

## No longer needed

None. No imports, modules, or nodes were removed. The representative identity
remains needed; this delivery completes its extension to all derived objects.

## Where the brief, the DAG or earlier work was wrong

No discrepancy found that requires a statement or definition change. This is a
partial proof delivery: the existing representative obligation remains for a
later worker, while its previously unfinished localization step is now proved.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
