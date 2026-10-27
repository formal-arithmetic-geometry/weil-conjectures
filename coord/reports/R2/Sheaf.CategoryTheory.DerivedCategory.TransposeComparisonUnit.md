## What changed

Replaced the sole `sorry` in
`CategoryTheory.Adjunction.derivedTransposeComparisonUnit` with a complete proof.
The homotopy conjunct is the symmetry of
`NatTrans.mapHomotopyCategoryPlus_mateEquiv_app`, with functoriality combining the
last two maps. The derived conjunct follows from
`Adjunction.derivedPlus_unit_app_fac`, naturality of
`Functor.rightDerivedFunctorPlusUnit`, functoriality of the localization, and the
homotopy conjunct. The degreewise conjunct follows by expanding `mateEquiv_apply`.
The statement, public imports, and all definitions are unchanged.

The library search used Lean Finder (the homotopy mate and natural derived-unit
comparison), Loogle (`CategoryTheory.Adjunction.derivedη_fac_app`), and grep
(`derived.*mate|mate.*derived|derivedη_fac_app`). Mathlib supplies the general
unit factorization; the existing source library supplies its bounded-below form
and the homotopy mate calculation. No additional statement or import is needed.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.Adjunction.derivedTransposeComparisonUnit`
(node `lem-trf-derived-transpose-comparison-unit`). All three conjuncts are proved.
No `sorry` remains in the item, and no holes or split statements were added.
The final single-file server compile passed without warnings in 2.9 seconds.

## No longer needed

None. Both existing public imports support the statement. Every planned proof
dependency is used: the termwise homotopy mate identity, the definition of the
ordinary mate, the bounded-below derived-unit identity, and naturality of the
right-derived comparison. The unit route is unchanged. No module or node is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The supplied proof plan is realized
using the existing source-library lemmas, without any injectivity hypothesis on
the target complex or inverse of the comparison map.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
