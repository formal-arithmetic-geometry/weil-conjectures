## What changed

Proved `CategoryTheory.Abelian.LeftResolution.leftResolution_bicomplex_total_exists`
without changing its signature, statement, imports, or docstring. The proof uses the
support instances already supplied by `LeftResolution.CochainComplexMinus`: resolution
rows are strictly supported in degrees at most zero, and the bicomplex and its mapped
image inherit the upper bound from `K.IsStrictlyLE b`. Evaluating the outer zero
complexes at the resolution degree gives the two first-degree support assertions.
Finally, `HomologicalComplex₂.hasTotal_of_isStrictlyLE` supplies both totals with bounds
`b` and `0`.

This implements the existing four-step node plan using its already proved source API.
The objectwise cochain-resolution instances supply the construction and row support;
the first-degree support instances use zero-morphism preservation, proved upstream
from `chainComplexMap_zero`; and `hasTotal_of_isStrictlyLE` is the already proved
existence component of the stated bounded additive-total argument. No preservation
isomorphism has to be constructed for this theorem. The node and unit route stay
unchanged.

Validation: the module and complete sandbox compile through `lcompile.py` without
errors or warnings. The original general hypotheses include arbitrary integer `b`,
the zero complex, and complexes concentrated in a single degree. No definitions,
public interfaces, or targets change.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.Abelian.LeftResolution.leftResolution_bicomplex_total_exists`
(node `lem-sfb-left-resolution-bicomplex-total-exists`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.

## No longer needed

None. No imports, nodes, or modules are pruned. The single public import provides the
bicomplex construction, its support instances, and the bounded totalization API.
The node's declared dependencies remain represented by these source implementations;
the proof does not add a dependency on the admitted additive-transport wrapper.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The detailed support and finite-diagonal
arguments of the plan are already proved in the imported source, so the Lean proof
can use those instances and the total-existence lemma directly.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
