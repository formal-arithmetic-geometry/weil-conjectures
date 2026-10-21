## What changed

Filled the three object-identification proofs in
`Sheaf.SixFunctors.FrobeniusPointTransportNatural` using the defining specifications
of the already recorded uniquely chosen functors. Rational pullback uses
`rationalDerivedPullback_existsUnique`; common-stage pullback uses
`commonStageDerivedPullback_existsUnique` followed by the rational object equality
at the object's literal coefficient stage; the qbar fibre equality uses
`pointQbarFibre_existsUnique`.

Only theorem proof bodies changed. The statements, definitions, imports and
blueprint unit route are preserved.

## Proved and sorry left

Closed three existing holes:

- `WeilConjectures.frobeniusPointRationalPullbackEq`.
- `WeilConjectures.frobeniusPointQbarPullbackEq`.
- `WeilConjectures.frobeniusPointQbarFibreObjEq`.

One original hole remains, unchanged:
`WeilConjectures.frobeniusPointTransport_natural`, attached to
`lem-weil-frobenius-point-transport-natural`. Its existing docstring and node retain
the complete naturality and scalar-compatibility argument. This is a partial
proof delivery for a module with several holes: three closed, zero added, zero
split off. The large naturality theorem is not claimed proved.

Validation: the module with the three completed proofs compiled through
`lcompile.py`. The delivery tool performs the final compile and preflight checks.

## No longer needed

None. No imports, nodes or modules are pruned. The remaining naturality theorem
still needs its recorded proof route. No auxiliary declarations from exploratory
proof work are included.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The three object equalities
need no new uniqueness results: the existing functor specifications already
provide the required object formulas. The common-stage equality requires
applying the rational object equality at the retained coefficient stage; its
right-hand object is not definitionally the integral-model object.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
