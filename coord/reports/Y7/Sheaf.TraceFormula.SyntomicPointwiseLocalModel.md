## What changed

Completed `AlgebraicGeometry.syntomic_pointwise_local_model` without changing its
statement, its existing docstring, any definition, or any public import.
Three proved private helpers carry the affine refinement, the affine fibre
comparison, and the passage from a principal coordinate localization to the
required open neighbourhood. The additional private proof import is
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections`; its evaluation
and residue-field section formulas identify the coefficient maps canonically.

The finite-presentation refinement first proves local finite presentation on
the original affine chart, then chooses an affine chart inside the inverse
image of the prescribed base open. `IsAffineOpen.arrowStalkMapIso` transports
the given flatness to the localized coordinate map. For the fibre comparison,
the affine pullback section square is a pushout; transport along the canonical
residue-field equivalence identifies its sections with `p.Fiber B` over
`p.ResidueField`. Contraction identifies the fibre prime, and affine stalk
localization gives the algebra equivalence needed by
`TraceFormula.ciLocalRingPrincipalNeighbourhood`. The original regular
sequence generates a proper ideal, hence lies in the ambient local ring's
maximal ideal. Apply
`Algebra.exists_relativeGlobalCompleteIntersection_of_syntomicAtPrime`, with
finite presentation witnessed at 1. Finally, the basic-open localization
isomorphism respects the actual `f.appLE` scalar map and gives the conclusion.

The existing DAG proof and its dependencies describe this same argument, so
no node change or new node is needed. Mathlib LeanFinder, Loogle and grep were
searched through `msearch.py`; only smooth analogues requiring stronger
hypotheses were found. Direct searches of both library roots and the relevant
Mathlib affine, fibre, finite-presentation and stalk APIs supplied the bridges.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.syntomic_pointwise_local_model`
(node `lem-trf-syntomic-pointwise-local-model`). Added 0 holes; split off 0.
There are no `sorry` tokens in the delivered module. Each private helper is
proved completely. The existing principal fibre-neighbourhood theorem remains
an imported dependency for subsequent work; this delivery does not claim to
have proved that dependency.

## No longer needed

None. All existing proof dependencies remain relevant to the implemented
argument. No import, node, module, public declaration, or blueprint unit step
is withdrawn. No additional unproved dependency was introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The affine stalk and pullback APIs in
Mathlib supply the compatibility statements needed to implement the original
five-step plan. No assumptions of global flatness, global finite presentation,
or complete-intersection fibres at other points were added.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
