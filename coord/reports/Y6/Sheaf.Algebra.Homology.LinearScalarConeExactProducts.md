## What changed

Replaced the proof hole of `CochainComplex.LinearScalarCone.exact_products` with an
explicit cochain calculation and localization descent, retaining the exact theorem
statement. The private helpers construct the scalar cocone/cone adjunction,
transport the existing coherent signed cocone shifts, and interchange the two
mapping-cone directions by the signed permutation `(a,b,c,d) ↦ (-a,c,b,d)`.
The localized adjunction proves product preservation; mapping-cone triangle
representatives prove exactness. Updated the existing DAG node to describe these
constructions and cite the existing signed cocone definitions and coherence.

## Proved and sorry left

Closed the single original hole in
`CochainComplex.LinearScalarCone.exact_products`. Holes closed: 1. Holes added: 0.
No `sorry` remains in the module or its private helpers. No statements were split off.
The complete proof compiled on the project server in 16.8 seconds. Removed
unused simplifier arguments and replaced a flexible simplification with its
explicit lemma list; delivery runs final compilation and preflight checks.

## No longer needed

Removed the direct public import
`WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit`: the declaration's
required interfaces already come through `LinearScalarCone`, and the proof does
not use homotopy-limit results. This import removal does not prune that module
from the transitive closure, since the scalar-cone definition still imports the
adic-tower interfaces. All originally declared proof dependencies remain used.
No module is withdrawn and no unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The original proof plan is valid but omitted the
cochain-level adjunction, signed four-coordinate permutation, and localization
glue. These are implemented directly, with no regularity or product-exactness
hypotheses. The product proof works for every existing product by right
adjointness and then specializes to the required countable shape.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
