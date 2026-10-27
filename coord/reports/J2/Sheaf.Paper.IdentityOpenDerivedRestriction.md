## What changed

Filled the composition proof in `Sheaf.Paper.IdentityOpenDerivedRestriction`.
On K-injective representatives, naturality moves the restriction across the first
resolution comparison. The existing restriction normalization and derived compositor
normalization reduce both sides to the localized underived composition equation,
which is checked degree by degree. K-injective representative extensionality then
extends equality to all objects. The proof follows step 3 of the existing node
`lem-sfb-identity-open-derived-restriction`; its route and dependencies are unchanged.
Two proved private helpers express the degreewise complex equation and the formal
normalization argument for arbitrary additive functors. Local irreducibility settings
keep the large sheaf functors from unfolding during proof checking. No signatures,
definitions, imports, or other modules are changed.

Validation: the complete module compiles without errors or warnings in 21.4 seconds
through the required server compiler, below the 60-second file limit.

## Proved and sorry left

Closed the one remaining hole:
`AlgebraicGeometry.ProEtale.CondensedRing.identity_open_derived_restriction_comp`
(node `lem-sfb-identity-open-derived-restriction`).

Added zero holes; split off zero holes. No `sorry` remains in the assigned module.
The main restriction theorem and the identity law were already proved on the base.

## No longer needed

None. All imports and the existing node dependencies remain needed. No module is
withdrawn. Searches of the source library and Mathlib found no shorter theorem
for the normalized composition of these particular unbounded derived functors.

## Where the brief, the DAG or earlier work was wrong

The source already proved two of the original three theorem holes; only the
composition law remained. Its existing node plan supplies the required argument.
No statement correction, new node, or forced adaptation is needed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
