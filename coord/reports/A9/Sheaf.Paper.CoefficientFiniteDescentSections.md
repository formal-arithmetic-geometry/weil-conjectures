## What changed

Restored the quarantined module `Sheaf.Paper.CoefficientFiniteDescentSections` from
`quarantine/Sheaf/Paper/CoefficientFiniteDescentSections.lean` as required by its rework row.
Preserved all three public signatures, public imports, coefficient constructions and the unit route.
Proved `AlgebraicGeometry.ProEtale.set_sections_filtered_colimit` by the existing plan:
construct the locally bijective presheaf-colimit comparison; refine covering sieves to finite affine
covers; obtain eventual equality at a common stage; glue finite local representatives, using
quasi-compact overlaps in the quasi-separated case and sectionwise stage injectivity otherwise.
The existing abelian and coefficient proofs now depend on this complete set comparison.

All new helpers are private and proved. They include the finite affine refinement, finite common
stages and arrows, local representatives and equality, eventual equality, stage injectivity, and
section representatives. Imported `Sheaf.CategoryTheory.LargeSetSheafification` for its already
proved universe-polymorphic local-bijection theorem and `Mathlib.CategoryTheory.Limits.Types.Filtered`
for the elementwise filtered-colimit API. Updated the node's proof and dependencies accordingly.
Single-file lcompile succeeds without warnings. The delivery tool supplies the declaration/axiom
probe and independent-review packet.
The static interface detector requires a record for the section-variable commands that scope the
new private helpers; see `coord/changes/A9-coefficient-sections-private-proof-scope.md`. The section
ends before the unchanged public declarations and exports no elaboration-context change.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.set_sections_filtered_colimit`
(node `det-lem-coefficient-finite-descent-sections`). Added 0 holes and split off 0 statements.
The restored module has 0 remaining `sorry`s. The pre-existing proofs of
`AlgebraicGeometry.ProEtale.abelian_sections_filtered_colimit` and
`AlgebraicGeometry.ProEtale.coefficient_finite_descent_sections` are preserved.

## No longer needed

Removed these private imports:

- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`;
- `Sheaf.CategoryTheory.SiteCoveringAxioms`;
- `Sheaf.Paper.CompletedCondensedCoefficients`;
- `Sheaf.Topology.ProfiniteCondensedRing`;
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.

The proof no longer needs node `lem-weil-pbc-site-sheafification-sections-local`; removed its
proof-dependency and obsolete top-level tool approval. Its generic local description is supplied
instead by the already proved `lem-weil-pbc-large-set-sheafification`, which accommodates the
independent diagram universe. This is a generic sheafification tool, not a replacement of a unit
step. The coefficient-colimit node `sk-prop-sfb-qlbar-colimit-x` remains needed: the existing proof
uses `AlgebraicGeometry.ProEtale.isColimitPadicAlgClRingObjCocone` directly from the source library,
so it does not need the completed-coefficient wrapper module. Definition nodes remain attached to
their existing declarations; no source-library declaration or quarantined archive is withdrawn.
No other declared proof dependencies are bypassed.

## Where the brief, the DAG or earlier work was wrong

The module was absent from `lean/` because of the cluster-restore quarantine, not because its
mathematics was withdrawn. Its rework source and Lean attachment have been preserved.
The node's prior proof-origin note that steps 1--5 remain open is now obsolete.
The finite affine refinement needs a covering certificate as well as joint surjectivity;
the proof constructs it over affine opens and composes covers by the site axioms.
The previously reviewed correction requiring quasi-separatedness or injective transitions for
surjectivity is preserved. Empty schemes, empty finite covers, and empty matrix dimensions are
included; filteredness provides a stage even for an empty family of representatives.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
