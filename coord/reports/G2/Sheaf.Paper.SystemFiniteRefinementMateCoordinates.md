## What changed

Added `Sheaf.Paper.SystemFiniteRefinementMateCanonical`, proving the evaluated
canonical bridge equation by applying `congrArg` to
`Realizations.properOpen.canonical` and simplifying functorial composition.
Added separate left and right normalization statements around that equation.
The left normalization is now proved by a generic natural isomorphism cancellation
lemma; the item theorem is composed from the two normalization statements and
the canonical bridge equality.

## Proved and sorry left

Proved: `WeilConjectures.IntegralSystemRealization.FiniteCoordinates.refinementMate` and
`WeilConjectures.IntegralSystemRealization.FiniteCoordinates.canonicalEvaluation`, and
`WeilConjectures.IntegralSystemRealization.FiniteCoordinates.lhsNormalization`.

Sorry left: `WeilConjectures.IntegralSystemRealization.FiniteCoordinates.rhsNormalization`.
These are the two strictly smaller transport/cancellation steps used by the
proved target theorem. Three new intermediate declarations were added in total,
with `canonicalEvaluation` proved and the two normalization declarations split
off for follow-up proof work.

## No longer needed

The left normalization no longer imports the canonical-evaluation module or
`AmbientProperOpenCalculus`; its proof uses only the finite-evaluation API and
canonical bridge isomorphisms. The target and the remaining intermediate
statements retain the finite evaluation, canonical bridge, and ambient declarations.

## Where the brief, the DAG or earlier work was wrong

The global build record lists the item as failing on three bad `Sheaf` imports,
while the restored source has those imports present and compiles in the sandbox.
The finite-coordinate cancellation was split into independent left and right
normalization statements so the target proof is a genuine transitivity argument.

## New nodes

Added `lem-sf-system-finite-refinement-mate-canonical-evaluation`, carried by
`Sheaf.Paper.SystemFiniteRefinementMateCanonical`. Added
`lem-sf-system-finite-refinement-mate-lhs-normalization` and
`lem-sf-system-finite-refinement-mate-rhs-normalization`, carried by the two
normalization modules. The canonical statement is proved; each normalization
statement is a proper subset of the target equation and remains `sorry`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SystemFiniteRefinementMateCanonical": "ad7b41f1724a04006b6f3b66030072150e48251e", "Sheaf.Paper.SystemFiniteRefinementMateCoordinates": "1e7b21112c63fa53a9bc161c2eb0b537c411e35d", "Sheaf.Paper.SystemFiniteRefinementMateLhsNormalization": "45b26c91b9e65a29fa98c5a0bf840b95ed81b901", "Sheaf.Paper.SystemFiniteRefinementMateRhsNormalization": "1bf0e71da00b17b536f055814e967032af9012cf"}, "results": {"Sheaf.Paper.SystemRefinementFiniteCoordinates": {"hash": "2f8c5d87e5b3d834c1c58d766645c95dcec97b1f", "status": "OK"}}, "seconds": 43, "time": "2026-10-28T02:33:48+0800", "transitive": 0, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
