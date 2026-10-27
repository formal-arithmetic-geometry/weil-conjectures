## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.space_invariant_open_quotient` in the assigned
module, preserving its complete public statement and every original public import.
Only this module and its own DAG node are changed.

Added proved private helpers for subsheaf reflection, injectivity of the kernel-pair
presheaf quotient, residue-field point comparison and naturality, the two invariant-open
pullback squares, point-surjectivity of representably surjective scheme maps, the
point-image calculation through an atlas, and representability under an isomorphism.
The reflection construction follows the existing private construction in
`EtaleRelationQuotient`; no shared file or definition is changed.

The proof uses the existing atlas-presentation, pullback-relation-presheaf,
restriction-quotient, finding-opens, and relation-quotient declarations. It constructs
both required sheafifications inside the given sheaf X, in the original universe,
before applying the declarations that require them. Equality of the two canonical
quotient maps follows from the coequalizer and reflection universal properties.

New private proof imports are `Sheaf.AlgebraicGeometry.EtalePullbackRelationPresheaf`,
`Sheaf.AlgebraicGeometry.ProperCurveModuli` (only its existing `mapPoint` definition),
`Mathlib.CategoryTheory.Sites.Subsheaf`,
`Mathlib.CategoryTheory.Limits.Types.Pullbacks`, and
`Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono`.

The empty open, full open, and empty atlas require no extra assumptions: the actual
scheme restriction and its pullbacks work for all three; a field point is lifted only
when a representative exists. The unit route is preserved; no realized unit statement
or step is bypassed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.space_invariant_open_quotient`
(node `lem-a1-space-invariant-open-quotient`). Added 0 holes; split off 0 statements.
There are no `sorry` declarations left in the delivered module and no new modules.
All private helpers have complete proofs. The theorem uses existing declared proof
dependencies, some still containing `sorry`, as authorized by stage 3.

Validation: the final module compiled through `lcompile.py` in 9.9 seconds, with no
errors or warnings. A source check confirms the public theorem signature is byte-for-byte
unchanged and the module contains no `sorry`. The DAG overlay has valid dependency IDs,
its `proof_deps` equals the union of the proof steps, and no cycle is reachable from
this item. Delivery preflight additionally runs its standard axiom and hole probes.

## No longer needed

The planned dependency `lem-a1-space-point-open-calculus`, module
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`, is not needed by this proof.
The required scheme-atlas point-surjectivity and image calculation are proved directly
from the scheme-test predicate and the residue-field representatives, so the much
larger conjunction of point-open-calculus results is not imported. Its dependency is
removed from this node's `proof` and `proof_deps`. This does not withdraw that module
or assert that its other consumers no longer need it.

No original Lean import is removed. All other original planned proof dependencies
remain in use; the presheaf-level restriction theorem and the existing definitions
used for the direct point calculation are recorded as additional proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and planned geometric argument are correct. The declarations
for atlas presentation and relation restriction take specified quotient sheaves and
units as inputs, so applying them alone does not construct the existential quotients
required here. The missing interface glue is supplied by an explicit subsheaf-closure
construction inside X, justified by the proved embedding of each presheaf quotient.
No existence axiom for global sheafification or arbitrary unproved witness is used.
The point-open-calculus dependency in the last planned step can be avoided as described
above. No shared interface change, consumer adaptation, or change record is required.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
