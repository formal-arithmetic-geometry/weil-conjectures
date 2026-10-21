## What changed

Withdrew the empty Sheaf re-export shim
`lean/Sheaf/AlgebraicGeometry/HigherDirectImageRawTrianglePullback.lean`.
Updated `Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors` to import the canonical
upstream extension directly. Its declarations and signatures are unchanged. The sandbox
`lcompile.py --all` compile succeeds (15.7 seconds on the last run).
Change record: `coord/changes/retire-higher-direct-image-raw-triangle-pullback.md`.
The consumer import closure is identical apart from the retired shim.

## Proved and sorry left

The item module had no declarations and no `sorry`s. Holes closed: 0. Holes added: 0. No `sorry` remains in the delivered files. This delivery retires the redundant shim rather than proving a declaration.

## No longer needed

The withdrawn Sheaf shim is no longer needed. No DAG node is deleted. The upstream
extension remains the canonical provider of the public raw triangle API, and all remaining
consumers receive it through their existing imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or proof route is wrong. The queue correctly classifies this
item as `retire`; after the upstream sync the Sheaf file is only a re-export shim. The
retire inventory records the upstream `rawTriangleMap` difference, so the upstream module
is retained and the consumer import is redirected rather than replacing its API.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
