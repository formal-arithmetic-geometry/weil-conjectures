## What changed

Proved `AlgebraicGeometry.specMap_isFiniteLocallyFree_of_basis` in
`Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum`, with its signature and public imports
unchanged. From the given basis, register module freeness, module finiteness, and module
finite presentation. Mathlib's `Algebra.FinitePresentation.of_finitePresentation` then
supplies algebra finite presentation. Apply the three spectrum criteria and assemble
`Scheme.Hom.IsFiniteLocallyFree`.

Added proof-only imports `Mathlib.LinearAlgebra.FreeModule.Finite.Basic` and
`Mathlib.RingTheory.Finiteness.ModuleFinitePresentation`. Updated the item's DAG proof
and proof origin to record the Mathlib implementation of the original algebra argument.
Read Stacks `morphisms.tex`, lemma-finite-flat (Tag 02KB), and `algebra.tex`,
lemma-finite-finite-type (Tag 0D46). The unit's realized statements and steps are retained.

Validation: the final proof with the reduced imports compiled through `lcompile.py`
in 2.4 seconds. `#print axioms` reported exactly `propext`, `Classical.choice`, and
`Quot.sound`. The diagnostic command was removed afterward. No added hypotheses:
empty bases, zero rings, and index universes distinct from the ring universe are covered
by the general Mathlib statements used here.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.specMap_isFiniteLocallyFree_of_basis`
(node `lem-weil-pbc-finite-free-algebra-spectrum`).
Added 0 holes; split off 0 statements. There are no remaining sorries in the item
and no new modules.

## No longer needed

Removed redundant proof-only imports `Mathlib.RingTheory.Finiteness.Defs`,
`Mathlib.RingTheory.Flat.Basic`, and `Mathlib.RingTheory.FinitePresentation`.
Their used APIs remain available through the more specific proof imports.

The hand-written polynomial multiplication-table quotient, coordinate inverse, and
separate empty-basis calculation in the old steps 3–4 are unnecessary: Mathlib's
module-to-algebra finite-presentation theorem already proves this argument.
All eight existing proof-dependency nodes remain used; no DAG nodes or project
modules are pruned. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statements or interface defects found. The DAG's long explicit algebra
presentation can be discharged with the Mathlib APIs already noted in its
`mathlib_candidate`. No definition, statement, or consumer adaptation was needed.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
