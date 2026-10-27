## What changed

Proved `AlgebraicGeometry.local_dimension_formula` in
`Sheaf.TraceFormula.LocalDimensionFormula`, with its statement and the existing
`dominantFunctionFieldAlgebra` definition unchanged. Added private proof imports of
`Sheaf.AlgebraicGeometry.DominantAffineChartData` and
`Sheaf.AlgebraicGeometry.AffineLocalDimensionTermComparison`.

The proof implements the current DAG's three steps. Apply the chart theorem to
all affine opens of the base, whose section rings are Noetherian. Use the term
comparison at the selected primes; install the supplied domain, Noetherian and
finite-type instances for the actual section map. Apply
`Ideal.height_add_trdeg_residueField_le`, rewrite the local dimensions and residue
transcendence degree, identify the canonical generic-stalk algebra by definitional
equality, and cast the affine inequality into `WithBot ℕ∞`.

LeanFinder, Loogle and Mathlib grep found no shorter general scheme-level formula.
The source-library search found field-base dimension formulas, which impose
stronger hypotheses and cannot replace the stated general-base affine reduction.
Checked Stacks Tag 02JU in `literature/stacks-project/morphisms.tex` against the
hypotheses and conclusion. The proof uses exactly the existing three proof
dependencies, so their node plan requires no change. No new declarations,
statements, definitions, or public imports.

## Proved and sorry left

Closed 1 of 1 item holes: `AlgebraicGeometry.local_dimension_formula`
(`lem-trf-local-dimension-formula`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. Its proof relies on the existing
named dependency theorems `AlgebraicGeometry.dominant_affine_chart_data`,
`AlgebraicGeometry.affine_local_dimension_term_comparison`, and
`Ideal.height_add_trdeg_residueField_le`, whose existing holes are unchanged.
This proves the requested assembly, not the transitive dependency closure.

## No longer needed

Removed the redundant private import
`WeilConjectures.Topology.PresheafModuleStalkFunctor`. None of the current DAG's
three proof dependencies is pruned; all three are used. No module is withdrawn.
The older docstring's localization, affine-point and transcendence-tower inputs
are needed inside the two comparison dependencies, not as direct proof imports
here; this delivery does not claim they are globally unused.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The existing theorem docstring describes the
pre-split affine reduction; the current DAG already factors that reduction into
the two available chart and comparison theorems, and the Lean proof follows it.
No unit statement or route changed.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
