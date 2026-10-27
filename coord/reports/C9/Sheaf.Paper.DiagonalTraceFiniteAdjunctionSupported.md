## What changed

Added the proof-only module `Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupportedAdditive`.
It records the direct-image construction as an additive homomorphism on the finite-arrow
Hom group, together with the supported-arrow normalization equation.  The original module
forgets the additive structure and assembles the required existential witness.  The original
statement and public imports are unchanged; the new import is proof-only.

## Proved and sorry left

The original declaration
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteAdjunction_supported`
is proved from the new additive-operation declaration.  The new declaration
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteAdjunction_supported_additive`
remains one named `sorry`, with node
`new-sfb-diagonal-trace-finite-adjunction-supported-additive`.

Thus one original hole is closed and one lower hole is split off.

## No longer needed

The original direct proof dependencies are no longer imported by the item module; the
parent proof uses the additive-operation module.  They remain statement dependencies of the
new lower node and are not globally withdrawn.  No additional module is pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG plan combines construction of the finite-arrow operation with its normalization in
one existential theorem.  The Lean statement is more usable when the construction exposes
its additive Hom witness explicitly; the parent then only performs the existential packaging.
No target statement or definition was changed.

## New nodes

`new-sfb-diagonal-trace-finite-adjunction-supported-additive` records the additive operation
construction and its normalization equation.  Its Lean module and node are included in this
delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupported": "4381b16dc8da89f713afcffb24d485d3704c00ad", "Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupportedAdditive": "532fcdd5131ce877c930ceb590f92754be404bb5"}, "results": {}, "time": "2026-10-28T03:30:30+0800", "transitive": 0, "version": 1}
```

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
