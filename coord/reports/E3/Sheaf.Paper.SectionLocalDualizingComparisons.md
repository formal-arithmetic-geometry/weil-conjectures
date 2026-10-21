## What changed

Proved `AlgebraicGeometry.Etale.SectionLocalDualizingComparisons.section_local_dualizing_comparisons`
in `Sheaf.Paper.SectionLocalDualizingComparisons`, preserving its full signature and docstring.
The two shifted-line clauses use smooth duality, exact inverse image, locally constant
pullback and geometric stalks. The fibre comparisons use the general smooth base-change
mate. The chart comparisons use `chartGeometry`, the affine-space adjunctions and the
existing counit-compatible locality constructions. Their maps are turned into isomorphisms
with `asIso`, so all required hom equalities are reflexive. Naturality of the section
compositor and inverse cancellation prove the normalization equation.

Added four fully proved private helpers: `section_line`, `isIso_sectionMap`,
`isIso_chartMap`, and `restriction_normalized`. The first two reuse the proved private
arguments in `NoetherianEtaleSectionSpecialization`; that module cannot supply them
publicly, and importing its larger specialization theorem would bypass this local argument.
The two new proof imports are `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality`
and `WeilConjectures.ConstructibleSheaf.Pullback`. Public imports and definitions are unchanged.
Updated the existing node's proof and dependencies to describe the actual Lean proof.

Validation: the complete module compiled through `lcompile.py` in 25.1 seconds with
exit code 0 and no diagnostics. Every Lean line is at most 100 characters.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Etale.SectionLocalDualizingComparisons.section_local_dualizing_comparisons`
(node `lem-trf-section-local-dualizing-comparisons`).
Added 0 holes; 0 holes remain in the delivered module. No statements were split off.
Existing dependencies with postponed proofs are used through their declared interfaces.

## No longer needed

Removed the private imports `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`,
`Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`,
`Sheaf.AlgebraicGeometry.SmoothTensorDuality`, and
`WeilConjectures.Compactification.NagataCompactification`. Canonical inverse-image and
base-change APIs are already public dependencies of the section comparison constructions;
the proof uses the upstream smooth-duality statement directly.

The item's direct proof no longer needs `lem-trf-smooth-section-centred-coordinates`:
it proves a property of every given Chart, rather than constructing a chart cover.
The direct geometric work associated with `lem-trf-section-rees-base-change-etale`,
`lem-pod-separated-finite-type-base-change`, `lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-open-immersion-etale`, and `thm-nagata-compactification` is already packaged
by `chartGeometry` and the local-comparison interface. These nodes were removed from the
item's direct proof dependencies and their obsolete tool-use approvals were removed where
present. Their uses inside existing dependency declarations remain: no global module
withdrawal or source-library declaration removal is claimed. Modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The DAG's coordinate-choice step was unnecessary for the Lean statement, which assumes an
arbitrary affine centred Chart and asks for its comparisons. The declared `chartGeometry`
already states the Rees/locality domain facts the planned proof would establish again.
The mathematical local construction and normalization route are preserved. The assigned
unit's realized list is empty and no unit statement or unit proof step was removed.
No statement or definition correction was needed. Empty schemes, zero coefficients and
relative dimension zero require no additional case distinction: the cover refinement and
isomorphism cancellation work in all of them.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
