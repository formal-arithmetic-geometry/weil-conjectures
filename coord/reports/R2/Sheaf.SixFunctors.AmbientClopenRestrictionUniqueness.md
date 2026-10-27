## What changed

Filled `AlgebraicGeometry.ProEtale.AmbientClopenRestriction.ambientClopenRestrictionUniqueness`
without changing its statement or the coefficient categories. Added private
helpers constructing an explicit binary-product gluing inverse on the ordinary or sequence
ringed site, transporting restriction to the published inverse image, and calculating the
restriction Hom equivalence through full faithfulness and adjunction conjugation. Reused the
published ordinary projector, open-unit, disjoint-extension and beta normalization APIs.
Updated the node proof to this route. Added the constructed public `restrictionPull`
comparison and refactored `restrictionSource` to use its inverse component, avoiding costly
repeated conversion through chosen inverse images. Its signature and mathematical map are
unchanged. The change record is `coord/changes/ambient-clopen-source-comparison.md`.
Also refactored `cartesianPull` to dispatch to the published `moduleSquareG` comparison
for the same square, in the inverse orientation. Its compositor formula is fixed by
`moduleSquareG_eq`; see `coord/changes/ambient-clopen-cartesian-comparison.md`.
The `transition` function also spells out its original linear-map application; see
`coord/changes/ambient-clopen-transition-application.md`. System `sections` now forgets
the scalar structure before evaluating the presheaf, retaining the same abelian section
functor while avoiding transport through a coefficient-ring equality. See
`coord/changes/ambient-clopen-section-evaluation.md`. No other library module is edited.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.ProEtale.AmbientClopenRestriction.ambientClopenRestrictionUniqueness`.
Holes closed: 1. Holes added: 0. Sorries left in the delivered Lean module: 0.
No split-off statements. All private helpers have complete proofs, and all definitions
construct their data. Imported declarations retain their existing proof status.

Validation uses the project-server `lcompile.py` and the required `deliver3.py` gate.
The public theorem signature and the complete `Assertion` definition are unchanged.
The construction covers empty clopen pieces and arbitrary system transitions: the empty
component uses subsingleton sections, and transitions are maps on the whole sequence site.

## No longer needed

The direct reconstruction of site localization and module sheafification in old steps 5–6
is replaced by the published strict/varying ordinary open-unit results. Removed the old proof-only
imports `ProEtaleIntrinsicExtensionByZero`, `ModuleSheafificationRestriction`, and
`ProEtaleWeaklyEtaleLocalization`.

The node no longer directly invokes `def-pc-sheaf-restrict-scalars`,
`def-weil-extension-by-zero`, `def-weil-pbc-composite-adjunction`,
`def-weil-proper-morphism`, `lem-coef-semilinear-derived-sections`,
`lem-pc-proper-monomorphism-closed`, `lem-pur-site-restriction-module-adjunction-exact`,
`lem-sf-open-tensor-normalization`, `lem-sfb-finite-type-composition-base-change`,
`lem-weil-pbc-conjugate-iso-unit-equation`,
`lem-weil-pbc-module-sheafification-restriction`,
`lem-weil-pbc-open-immersion-base-change`, `lem-weil-pbc-proper-base-change`,
`lem-weil-pbc-proper-to-separated`, or `lem-weil-proetale-weakly-etale-localization`.
Geometry uses the existing squareLift clopen API and Mathlib instances. The categorical
composite-adjunction and conjugation identities are Mathlib lemmas; the ordinary beta
normalization comes from the existing strict/varying APIs. System gluing is constructed on
the coefficient-sequence ringed site, so no derived evaluation or derived faithfulness is used.
Removed obsolete top-level tool-use entries for semilinear-derived-sections,
open-tensor-normalization, module-sheafification-restriction,
proetale-weakly-etale-localization, and site-restriction-module-adjunction-exact.
These are reductions in this node's direct proof dependencies; no claim is made that their
modules are unused elsewhere in the library, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. Scalar evaluation uses the existing
`WeilConjectures.SemilinearSections.evaluation_smul` theorem from
`Sheaf.Paper.SequenceOpenScalars`, since ring evaluation transports its scalar
structure along the coefficient-ring equality. The planned argument can be implemented using the now-published
ordinary strict/varying APIs; there is no need to reconstruct their proofs here. The explicit
binary product retains literal section pairs, making scalar and transition compatibility part
of the construction. The unit route is preserved and no new nodes are introduced.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
