## What changed

Proved `CategoryTheory.Mod.sheaf_scalarCoordinateLimitCriterion` in
`Sheaf.CategoryTheory.ScalarCoordinateLimitCriterion`, without changing either existing
signature or the definition of `ScalarCoordinateLimitCriterion`.

The shorter proof uses the source library's creation of internal-module limits. The
constant-diagram and limit functors preserve limits; transport across the supplied
natural isomorphism and cancellation of the B-module forgetful functor finish the proof.
The additivity conjunct follows from the existing canonical sheaf-tensor closedness result.
The arbitrary additivity instance quantified by the criterion is retained in the proof.

Added proof imports `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits` and
`Mathlib.CategoryTheory.Adjunction.Limits`. Updated the node's proof, proof dependencies,
proof origin and obsolete tool-use approval to match. Public imports are preserved.
Compilation passed through `lcompile.py`; the argument includes n = 0 and empty diagrams.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.Mod.sheaf_scalarCoordinateLimitCriterion`
(node `lem-sfb-scalar-coordinate-limit-criterion`).

No holes remain in the item. No holes added and no statements split off.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`.

The proof no longer needs nodes
`def-weil-pbc-internal-abelian-sheaf-module-equivalence` or
`lem-weil-pbc-module-sheaves-limits-sectionwise`: internal-module limits are already
constructed directly in the source library. Removed the obsolete approval of the former
from `tool_uses`.

The separate node `lem-sfb-conservative-left-exact-reflects-finite-limits` and the
restriction-specific preservation/conservativity calculation are unnecessary: cancel
`Mod.forget B` directly, using its existing creation of limits. The module-object and
scalar-restriction definitions remain available through the existing public imports.
No modules are withdrawn; these pruning claims concern this item's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The seven-step plan was mathematically valid but missed the proved source-library
`CategoryTheory.Mod.createsLimit`. It removes the need to transfer to sectionwise module
sheaves or prove restriction conservativity. Mathlib also already proves that constant
diagrams and the limit functor preserve limits, so the coordinatewise calculation can
be replaced by their composition. The unit's finite-free scalar-coordinate route and
all hypotheses and conclusions stay intact.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
