## What changed

Proved `AlgebraicGeometry.ProEtale.OpenSquareClosedUnit.closed_unit_triangle` in
`lean/Sheaf/Paper/OpenSquareClosedUnitTriangle.lean` by the existing source-library
recollement API. The actual open counit gives the specified isomorphism `c` through
the adjunction triple. Mixed vanishing and joint zero detection on homology give
the open essential-image criterion. Unique recollement connecting maps assemble
into a natural transformation; explicit triangle transport and the triangulated
composite give the requested arrows. Four fully proved private categorical helpers
implement the essential-image, naturality and first-vertex and lower-bound transport arguments.

The public signature, all three helper definitions, and every public import are
unchanged. No other Lean module changes. Updated the existing node's proof route,
proof dependencies and origin. The enclosing unit has no realized statement or
step nodes; this replaces only its below-unit localization input.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.OpenSquareClosedUnit.closed_unit_triangle`
(node `lem-sfb-open-square-closed-unit-triangle`). Holes closed: 1 of 1.
Holes added: 0. Split off: 0. No `sorry` remains in any delivered Lean declaration.
The four private helpers are fully proved, and all objects and natural
transformations in the proof are constructed. The connecting maps are determined
uniquely by the distinguished-triangle property, rather than chosen from a mere
existence statement.

## No longer needed

Removed these twelve private imports from this item:

- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus`
- `Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit`
- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`

The replacement route removes these thirteen direct proof dependencies:

- `lem-sfb-alpha-iso`
- `lem-sfb-internal-module-operations-transport`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `det-prop-sfb-module-pullback-exact-main`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-sfb-exact-open-closed-unbounded-calculus`
- `lem-sfb-kinjective-direct-image-open-word-model`
- `lem-sfb-proetale-open-restriction-counit`
- `lem-sc-derived-adjunction-from-underived`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-sf-derived-homology-long-exact`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`

The proof no longer constructs a transported short exact sequence or uses an
explicit K-injective open-word model. Generic source adjunction/recollement and
triangle zero/isomorphism lemmas provide those steps directly. The retained
imports may still use some removed nodes transitively; this packet does not
withdraw any module or claim those modules are globally unreachable. Removed
only the corresponding obsolete top-level `tool_uses` approvals, preserving the
order of the retained entries. New dependency approvals are left to review.

## Where the brief, the DAG or earlier work was wrong

The seven-step plan is valid but longer than necessary: the source recollement
API already constructs the triangle with its exact unit and counit. The existing
condensed recollement theorem supplies its underived closed exactness and full
faithfulness; its bounded-below triangle is not confused with the required
ordinary unbounded derived triangle. The final equivalence is the standard
triangle criterion, so no separate cohomology long-exact-sequence argument is
needed. The source-library declarations are preserved without modification.
The current module exists live despite its historical rework/quarantine row;
its Lean attachment and statements have been preserved.

Edge cases remain covered without exclusions: the empty open or closed part,
`M = 0`, zero coefficients, and the empty target of `i`. The proof uses only
complementarity, exactness and categorical identities, so each construction
still applies in those cases. No new hypotheses or definition repairs.

Validation: the complete module compiled in 31.5 seconds with zero errors and no
remaining holes. Removed profiling and fixed the two reported style warnings
before the delivery tool's final compile and preflight checks. The local heartbeat
allowance covers comparison of canonical derived composites; the 60-second
compiler limit is unchanged.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
