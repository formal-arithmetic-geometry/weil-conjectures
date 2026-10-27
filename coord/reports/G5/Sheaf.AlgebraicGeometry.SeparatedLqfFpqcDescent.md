## What changed

Filled `CategoryTheory.Over.DescentDatum.isEffective_of_isSeparated_isLocallyQuasiFinite_fpqc`
in `Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent` without changing its statement.
The existing Stacks/Mathlib comparison supplies local quasi-finiteness and local finite
type. Base-change and composition instances give these properties and separatedness
for each quasi-compact open over an affine target open; compactness gives a quasi-compact
morphism. Zariski's Main Theorem then supplies quasi-affineness, so the existing
`isEffective_of_indQuasiAffine_fpqc` proves effectivity.

Replaced two proof imports by
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison`. Updated the item's
DAG proof, dependencies, and obsolete tool-use entries to match. No public imports,
signatures, definitions, or other existing modules changed. Validation: the final file compiled cleanly through `lcompile.py` in 2.7 seconds.
The source proof works
also for empty opens and an empty total scheme, and requires neither quasi-compactness
of the original morphism nor separatedness of the bases.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Over.DescentDatum.isEffective_of_isSeparated_isLocallyQuasiFinite_fpqc`
(node `lem-a1-separated-lqf-fpqc-effective-descent`).

No `sorry` remains in the item. Added 0 holes and 0 split-off statements. This proof
uses existing declarations, whose transitive proof obligations are unchanged.

## No longer needed

Removed explicit proof imports
`WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE` and
`WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`.
The item no longer directly uses nodes `lem-weil-pbc-lqf-restriction-to-opens` and
`lem-weil-pbc-lqf-locally-finite-type`; the comparison theorem supplies Mathlib's
properties once, and its permanence instances handle the pullback and open immersion.
Removed these two obsolete top-level tool-use approvals from the item's node.
The latter finite-type theorem is still used transitively by the comparison module;
no claim is made that either upstream module can be removed from the library.
No modules are withdrawn. The unit's route and the ind-quasi-affine descent dependency stay.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's open-restriction step can be implemented more
simply by the existing Stacks/Mathlib comparison followed by typeclass instances,
without writing an isomorphism between the pullback and a restricted open subscheme.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
