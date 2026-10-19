## What changed

Proved `AlgebraicGeometry.ProEtale.isIso_finiteComparisonGlobalSections` without changing
its statement or either canonical definition. Added proof-only imports of
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` and
`WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`.

The finite-level theorem supplies exactness. Evaluation of the invertible ordinary
adjunction unit gives precisely the isomorphism underlying the specified section map.
The existing global-sections vanishing lemma sends injective etale sheaves to
pro-etale-section-acyclic objects, since injectives have zero positive derived etale
sections. The proved generic right-derived base-change criterion then proves
invertibility of exactly `finiteComparisonGlobalSections`, not an arbitrarily chosen map.
The node now records this route.

Validation: the retained proof was checked against the current library sources and
single-file `lcompile.py` completed cleanly again (2.4 seconds) on 2026-10-19. The inclusion
of the acyclicity module passes `import_direction.py may`. The required delivery dry run
passed: commit `5c1719b8b0` compiles and passes preflight (CODEX review).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.isIso_finiteComparisonGlobalSections`
(node `lem-weil-pbc-comparison-global-cohomology`).

Added zero holes; split off zero theorems. No `sorry` remains in the delivered Lean module.
The proof uses existing library declarations and retains their existing upstream
obligations; it does not claim that the whole target import closure is axiom-free.

## No longer needed

Removed these original proof-only imports:

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension`

The site-comparison definitions remain available through the retained public imports.
Removing the original public derived-site-comparison import failed because the statements
need its public site and coefficient interfaces; it was restored. No module is withdrawn.

The parent no longer directly invokes
`thm-weil-pbc-site-comparison` / `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
or `lem-weil-pbc-derived-sections-pushforward` /
`WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension`.
Instead, the existing source vanishing theorem packages the Leray and derived-unit
argument already needed here. The derived-sections node remains a dependency of that
source theorem and is not claimed globally pruned. No unit statement or realized unit
proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node describes the correct Leray/unit argument but omits the already-proved
source-library vanishing consequence, which allows the generic base-change criterion
to apply directly. The declaration is not accessible through the item's original
imports, so it needs the explicit proof-only import.

Mathlib searches were run with LeanFinder, Loogle, LeanSearch and grep. None gives the
site comparison itself. Loogle does find positive derived vanishing on injectives.
Repository searches locate the exact vanishing lemma and generic base-change criterion.
No mathematical statement was changed and no definition repair was necessary.

The generic node `src-right-derived-functor-plus-base-change-of-right-acyclic` and clause 1
of `lemma-weil-pbc-leray-acyclicity` are used as proved homological-algebra tools. They
replace no geometric or chapter-level proof step.

## New nodes

`src-weil-pbc-comparison-global-sections-vanishing` attaches the existing declaration
`AlgebraicGeometry.ProEtale.isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj`
in `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`. It records the source
lemma actually used in the proof, introduces no Lean declaration and no hole, and is
strictly a vanishing consequence used to verify the acyclicity hypothesis of the generic
criterion. Its source proof was read in full: Leray for terminal sections, the canonical
derived comparison unit, then homology and transport of the zero object.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
