## What changed

Proved all three outstanding theorems in `Sheaf.Paper.AdicPurityObjects`.
`purAdicCoefficientUnit` computes the characteristic of the finite base field from
its cardinality, transports it to the algebraic closure, and uses the distinct
coefficient prime to obtain a unit. The unit maps through the affine global-section
isomorphism and the structure morphism, so the proof also covers the empty scheme.
`purAdicResidueUnit` maps that global unit through the canonical residue evaluation.
`purAdicReductionFiniteTor` extracts constructibility at the chosen positive level
and specializes the common integral Tor interval to that level.

The statements, definitions, visibility, public imports, and existing proof route
are unchanged. The proofs implement the existing declaration docstrings; no DAG
route changes or new declarations are needed. Remote single-file compilation
passed without warnings in 11.5 seconds.

## Proved and sorry left

Closed three holes, all belonging to `def-pur-adic-purity-objects`:

- `WeilConjectures.purAdicCoefficientUnit`.
- `WeilConjectures.purAdicResidueUnit`.
- `WeilConjectures.purAdicReductionFiniteTor`.

Zero holes remain in the item. Zero holes added; zero statements split off.
The proofs use Mathlib and the existing predicate definitions, without invoking
any other project's theorem with an unfinished proof.

## No longer needed

None. No imports added or removed, no new proof dependencies introduced, and no
nodes or modules made unreachable. The existing public imports are retained as
the module's statement and construction interface. In particular the proofs do
not need the stronger integral-operation preservation or normalized-tower
effectivity theorems from those imported modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing docstrings describe sufficient direct
proofs. The node has no planned proof dependencies, and these proofs need none.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
