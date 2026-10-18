## What changed

Proved `AlgebraicGeometry.Etale.properOpenSectionProperties` in
`Sheaf.AlgebraicGeometry.ProperOpenSection`, preserving its exact statement,
visibility, docstring and imports. The two projection equations follow from
`properOpenSection` and the pullback lift equations. The first projection is an
open immersion by base change of `j₂`; cancellation against that projection
(`IsOpenImmersion.of_comp`) proves that the section is an open immersion.
Properness of the second projection supplies separatedness, so the existing
`open_section_clopen` theorem gives its clopen image. Injectivity of the first
projection and the first projection equation give the section's range equality.
`IsOpenImmersion.range_pullbackFst` gives the projection's range equality.

The five steps and all dependencies of the existing DAG plan are retained, so
no node update is needed. The unit's realization record has no prescribed
statement or proof steps bypassed by this argument. The module compiled cleanly
through `lcompile.py` (2.2 seconds).

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Etale.properOpenSectionProperties`
(node `lem-weil-pbc-proper-open-section`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
This is a proof from the declared dependencies, including the existing theorem
`AlgebraicGeometry.open_section_clopen`
(node `lem-weil-pbc-open-section-clopen`), whose proof remains `sorry` in its
unchanged module; this delivery does not claim that dependency is proved.

## No longer needed

None. No imports, dependency nodes or modules are removed. All existing proof
dependencies are used, through the section definition, pullback API, open
immersion API, proper pullback instances, and clopen-section theorem.
The existing holed `properOpenSectionGeometry` is not used by the proof; only
the constructed `properOpenSection` from its module is used.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. Mathlib already supplies the
cancellation and image formulas needed to implement the geometric steps, so no
new intermediate statements are necessary. LeanFinder returned the constituent
pullback range formulas; grep located those and `IsOpenImmersion.of_comp`.
The initial Loogle query returned a parse error; local source inspection supplied
the exact signatures. No definitions or statements were changed.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
