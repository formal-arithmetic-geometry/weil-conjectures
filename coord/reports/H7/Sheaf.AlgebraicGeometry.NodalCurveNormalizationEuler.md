## What changed

Proved `AlgebraicGeometry.Scheme.nodal_curve_normalization_euler` in
`Sheaf.AlgebraicGeometry.NodalCurveNormalizationEuler`, with its original signature and
public imports unchanged. The normalization-quotient theorem supplies the exact sequence
and the node count. The proof establishes finite presentation and finite-dimensional
cohomology for its terms, applies Euler additivity, and uses the existing numerical affine
pushforward comparison. A disjoint-open-cover calculation gives the sum over components.
The existing `eulerChar_unit_eq` and `genus_eq_arithmeticGenus` calculate each component's
contribution.

Six fully proved private helpers implement normalization transport across isomorphisms,
uniqueness of the reduced closed component, the component Euler formula, invariance under
scheme isomorphism, the coproduct Euler formula, and the canonical normalization
presentation. In particular, the arbitrary integral closed component presentations in the
original statement are actually compared with the canonical reduced components; no
identification is assumed.

Proof imports add the existing affine numerical comparison, closed-immersion factorization,
smooth-relative-dimension criterion, curve Euler/genus formulas, finite coproduct morphisms,
and finite-pushforward finite presentation APIs. The node's proof, proof dependencies and
proof origin describe this realization. No source-library declarations or other modules
are edited; no definitions or statements are changed.

The new generic tools recorded in the proof dependencies are
`lem-pc-euler-characteristic-well-defined` (proper coherent finiteness/vanishing),
`lem-sbc-relative-normalization-universal-property` (a Mathlib leaf),
`lem-sc-normalization-exists` (finite normalization and dimension preservation),
`lem-sc-riemann-roch` (only its already-proved structure-sheaf specialization), and
`lem-pc-genus-agrees-sc` (the genus convention conversion). These are used below the unit's
normalization/Euler-characteristic step; no unit statement or realized step is bypassed.
Maintainer tool approvals have not been added or reordered.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.nodal_curve_normalization_euler`
(node `lem-trf-nodal-curve-normalization-euler`).
Added 0 holes. Split off 0 statements. There are no remaining `sorry` declarations in the
item and no new modules. This is a proof from existing library dependencies, including
`nodal_normalization_quotient`; it does not assert that those dependencies' transitive
holes are closed.

Remote single-file compilation succeeds. The supplied theorem statement was compared
verbatim with the original. Empty node sets are covered by the finite-sum/skyscraper API;
self-nodes are counted once through the original quotient theorem. The coproduct helper
also handles an empty component index. The component comparison uses reducedness, so it
never mistakes a nonreduced thickening for the reduced irreducible component.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge`: the numerical affine
pushforward theorem in `Cohomology.Affine.AffineMorphism` gives precisely the invariant
needed, with no explicit edge-map compatibility argument. The DAG retains the mathematical
affine-cohomology-comparison dependency and explicitly identifies this alternate existing
Lean API. The upstream edge-map declaration and its dependencies are preserved.

Removed the direct proof dependency and obsolete top-level tool approval for
`lem-sc-noetherian-cohomology-above-dimension`: the component calculation uses the already
proved curve specialization instead of applying the general dimension-vanishing theorem.
Removed the direct proof dependency and obsolete top-level tool approval for
`lem-weil-pbc-finite-type-over-noetherian`: local Noetherian instances come from Mathlib;
there is no separate application of that recorded theorem. These are direct-route removals,
not claims that the nodes are absent from all transitive library dependencies.

No modules are withdrawn. The normalization-quotient node, global-functions calculation,
Euler additivity, genus and Euler definitions, and finite/affine-morphism facts remain
needed. The unit's own route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The plan omitted the Lean identification between the supplied
integral closed component presentations and the canonical reduced components. This is now
proved, together with compatibility of their normalization maps. The planned split-direct-sum
filtration is replaced by the existing disjoint-open-cover Euler formula, and the expanded
component cohomology calculation by the existing structure-sheaf Euler formula. No new
mathematical assumptions or unproved intermediary statements are introduced.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
