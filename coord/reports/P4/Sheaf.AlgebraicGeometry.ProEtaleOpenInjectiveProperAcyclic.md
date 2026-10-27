## What changed

The assigned theorem now has a complete proof by composition. It obtains an
`OpenProperClopenWitness` for the commutative proper/open square and applies the
acyclicity theorem from that witness. I added the two supporting modules
`ProEtaleOpenProperClopenWitness` and
`ProEtaleOpenInjectiveProperAcyclicFromWitness`, and removed the unused
proof-only imports from the assigned module.

## Proved and sorry left

The declaration
`AlgebraicGeometry.Scheme.isZero_higherDirectImage_open_injective_of_proper`
was proved (one sorry closed). Two strictly smaller argument statements were
split off and remain sorry:

- `AlgebraicGeometry.Scheme.exists_openProperClopenWitness`, the geometric
  fibre-product and clopen-factorisation statement (node
  `lem-sp-proetale-open-injective-proper-acyclic-geometry`);
- `AlgebraicGeometry.Scheme.isZero_higherDirectImage_open_injective_of_proper_of_witness`,
  the sheaf-theoretic acyclicity statement assuming that geometric witness
  (node `lem-sp-proetale-open-injective-proper-acyclic-from-witness`).

No definition contains a sorry.

## No longer needed

The assigned theorem's proof no longer directly imports the former proof-only
chain for the seven-step argument: the open/closed sequence, derived
restriction, extension-by-zero base change, K-injective resolution, local
weak-contractibility, and boundary-cohomology modules are now dependencies of
the split-off acyclicity theorem rather than of this module. The corresponding
old proof-dependency entries were removed from the assigned node and its
obsolete `tool_uses` list was cleared. The public imports required by the
assigned theorem's signature were retained.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof was too large to express in the assigned theorem
without intermediate interfaces. The geometric clopen factorisation and the
sheaf-theoretic/local boundary argument are separate mathematical parts, so I
recorded each as its own strictly smaller theorem and made the assigned proof
a real composition of them. No target statement or definition was changed.

## New nodes

`lem-sp-proetale-open-injective-proper-acyclic-geometry` records the existence
of the fibre-product/clopen witness and is attached to
`ProEtaleOpenProperClopenWitness.lean`.

`lem-sp-proetale-open-injective-proper-acyclic-from-witness` records the
acyclicity argument once that witness is supplied and is attached to
`ProEtaleOpenInjectiveProperAcyclicFromWitness.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic": "3e441734d99cc0f9c8b3e987efccfec7fac480fb", "Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicFromWitness": "8d216ad4c5c7ec7026d145f2d611ab2ac11c6a25", "Sheaf.AlgebraicGeometry.ProEtaleOpenProperClopenWitness": "c91b80cfc9384bba9d3b0e09f9928d9d7c56cb13"}, "results": {"Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport": {"hash": "6e537a06aeb729b14ade4c84728507d2c0d78b71", "status": "OK"}}, "seconds": 24, "time": "2026-10-28T06:29:43+0800", "transitive": 0, "version": 1}
```

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
