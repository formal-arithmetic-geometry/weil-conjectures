## What changed

Refactored the proof of `Rep.nonempty_equiv_invariantResolution_inhomogeneous` so the
universal delta-functor comparison is constructed as a local proof term at the point
where `R`, `T`, and the degree `q` are fixed. Removed the duplicate top-level private
helper `universalDeltaFunctor_iso_all`, whose statement duplicated an existing library
comparison theorem and caused the prior delivery return. The public theorem statement,
imports, docstring, and all mathematical dependencies are unchanged.

## Proved and sorry left

`Rep.nonempty_equiv_invariantResolution_inhomogeneous` remains fully proved and has no
`sorry`. This delivery adds no declarations and leaves zero `sorry`s in the item module.

## No longer needed

The removed top-level helper declaration is no longer needed; its proof is carried out
locally in `comparison0`. No imports, DAG nodes, or mathematical dependencies were
pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery's proof was complete, but its generic top-level universality helper
was rejected by duplicate-statement checking. The comparison is still required; making
it local avoids exposing a duplicate declaration while preserving the same uniqueness
argument and result.

## New nodes

None.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
