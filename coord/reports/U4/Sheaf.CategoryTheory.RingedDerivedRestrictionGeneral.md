## What changed

Proved `CategoryTheory.ringedOverFunctor_exactGeneral` in
`Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`, with its signature unchanged.
The proof is sectionwise for addition. It identifies the underlying abelian sheaf of a
restricted module with restriction of its underlying abelian sheaf, obtains finite-limit
preservation by reflection through `SheafOfModules.toSheaf`, and proves preservation of
epimorphisms using local surjectivity and cocontinuity of `Over.forget U`. Mathlib's
`preservesHomology_of_preservesEpis_and_kernels` and
`preservesFiniteColimits_of_preservesHomology` then give finite-colimit preservation.
Only proof imports were added; all definitions and public imports are unchanged.

Validation: the module compiled successfully through `lcompile.py` in 12.5 seconds.
`#print axioms` for all four public declarations reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. All lines have at most 100
characters; the two source-library proof imports were checked for import cycles.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.ringedOverFunctor_exactGeneral`
(node `def-weil-pbc-ringed-derived-restriction`). Zero holes added, zero split off,
and zero sorry declarations remain in the delivered module. This is a proof, not a
decomposition. The argument uses proved Mathlib and source-library lemmas only.

## No longer needed

No original imports or DAG dependencies were removed. The definition node has empty
`proof` and `proof_deps`; the sectionwise/local-surjectivity proof follows the existing
exactness docstring. No unit statement or proof step changes.

The small-category results `CategoryTheory.ringedOverFunctor_preservesFiniteColimits`,
`SheafOfModules.overFunctor_exact` (module
`Sheaf.CategoryTheory.FiniteTypeRestrictionExact`), and
`CategoryTheory.localCoefficientRestriction_exact` are not needed for this proof.
Their universe-specialized Kan-extension route is unnecessary here; no corresponding
proof imports were added. The existing public `RingedDerivedRestriction` import still
provides the module's exported derived-category and restriction APIs.

## Where the brief, the DAG or earlier work was wrong

The node is a definition node and has no numbered proof plan or declared proof
prerequisites beyond its statement dependencies. The actual obligation is the named
exactness theorem required by its concrete derived functor. It is valid with independent
site, ring, and module universes: local-surjectivity preservation avoids requiring
large right Kan extensions in the coefficient category. No statement repair is needed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
