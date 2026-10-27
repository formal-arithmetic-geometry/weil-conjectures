## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientOpenClosedKernelIso` in the assigned
module, keeping its statement and public imports. The added helpers are private and
proved. No shared definition or consumer interface changes.

The proof search found generic kernel-isomorphism APIs but no direct geometric
localization theorem at these coefficient universes. The existing affine
closed-site adjunction is used as a proved tool; the open-closed sequence remains
the unit route.

The proof works on the original pro-etale sites with the independent coefficient
universe. It identifies open inverse image with restriction by uniqueness of left
adjoints and obtains the invertible open-extension unit from the adjoint triple.
The existing affine closed-site adjunction gives a fully faithful closed direct
image. A module-valued local-section argument proves joint detection by the closed
and quasi-compact open restrictions. Exactness follows after applying these two
restrictions, giving the open counit as a categorical kernel of the closed unit.

The final isomorphism transports this kernel through the AsSmall sheaf equivalences.
The unit equation for uniqueness of left adjoints explicitly relates the transported
unit to `coefficientFixedCanonicalAdj`; `kernel.mapIso` then identifies their kernels.
No data is selected from an unproved mere-existence statement.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.coefficientOpenClosedKernelIso`
(node `lem-pe-coefficient-open-closed-kernel`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
Validation: launcher single-file compilation passed in 26.5 seconds with no warnings.
Instance exclusions are confined to individual declarations. The delivery tool
compiles the final import cleanup and probes every added declaration for axioms.

## No longer needed

The proof does not need `lem-sf-proetale-open-closed-sequence` or import
`Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence`. Its coefficient universe is
fixed to `u+1`, whereas this item allows independent `max(v,u+1)` coefficients.
The required localization argument is proved here at the needed universes.
This prunes that node from this item's proof dependencies only; its declaration
and other consumers remain intact.

The weakly contractible principal-open/localization covering in the original plan
is unnecessary for this proof: joint detection and the adjunction identities prove
the kernel assertion. The unit's open-closed localization route is retained.
The redundant direct proof imports
`WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty` and
`WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction` are removed;
their used APIs are already publicly imported through the detection module.
No public import is removed; no existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The stated open-closed sequence cannot be specialized directly to this theorem's
independent coefficient universe. The section-detection and categorical localization
proofs do work there, with explicit sheafification, Kan-extension, and AB5 instances.
Some of the needed arguments already exist as private helpers in
`CoefficientFixedClosedUnitEpi`; private helpers cannot be reused through an import,
so their proofs are reproduced inside this item without changing that module.

The proof treats empty open and closed schemes, a zero coefficient ring, and
nonreduced closed subschemes uniformly. It does not infer a scheme isomorphism from
surjectivity of a closed immersion on underlying points.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
