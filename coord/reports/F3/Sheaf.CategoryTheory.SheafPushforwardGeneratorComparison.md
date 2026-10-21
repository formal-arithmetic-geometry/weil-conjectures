## What changed

Proved `CategoryTheory.Sheaf.generatorRestriction_comparison` in
`Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison`, preserving its signature
and all existing definitions and docstrings. Proved private helpers implement the
node's existing four-step argument: convert the package's heterogeneous equations
into casted Hom equations; identify the inclusion's adjunction mates with its actual
generators; expand lax composition and counit transport; cancel the inverse counits
against the sheafification tensorator; and apply the sheafification Hom equivalence.
The tensor and unit uniqueness clauses use the package's existing Hom equality tests.
No existence theorem is used to choose data.

Removed the redundant direct public import of
`Sheaf.CategoryTheory.SiteCoveringAxioms`; it remains publicly available through
`Sheaf.CategoryTheory.BraidedSheafTensorGenerators`. Change record:
`coord/changes/F3-sheaf-pushforward-generator-comparison-import.md`.

The cleaned module compiled through `lcompile.py` in 10.4 seconds without warnings.
The delivery tool additionally runs its compilation and axiom probes. All writes
are confined to the assigned sandbox.

## Proved and sorry left

Closed one of one original holes:
`CategoryTheory.Sheaf.generatorRestriction_comparison`
(node `lem-sfb-sheaf-pushforward-generator-comparison`).
Added zero holes, split off zero theorems, and left zero `sorry` declarations in the
item or delivery. Every new private helper is proved. This is a proof, not a
redistribution of holes to new statements.

## No longer needed

Removed the unused direct import `Sheaf.CategoryTheory.SiteCoveringAxioms`.
This removes only a duplicate import edge; the module itself remains a transitive
dependency. No DAG dependency, node, or module is pruned. All three existing
proof dependencies remain used: `lem-sfb-braided-sheaf-tensor-generators`,
`def-weil-pbc-sheafification`, and `lem-sfb-monoidal-adjunction-mates` (the latter
through Mathlib's right-adjoint lax monoidal construction). The unit route and
existing node proof plan remain unchanged, so no node update is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The prescribed equalities of tensor objects
require explicit casts: the generator maps are not pointwise evaluations of sheaf
tensor products. The proof keeps those casts throughout. The stage-2 review's
advisory that the direct site-axioms import is unused is confirmed and addressed.
The historical F3 return concerns another module, not this item.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
