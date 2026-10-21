## What changed

Proved `AlgebraicGeometry.Scheme.integralConstructible_hom_sums` with its signature and
public imports unchanged. The proof shifts the supplied family by `q`, applies the existing
integral bounded-below compactness theorem, and takes zeroth cohomology. A coproduct of the
scalar-valued RHom objects is constructed from complex representatives using
`derivedModuleDirectSums`; `derivedModuleHomology_coproduct` preserves its colimiting cofan.

Three proved private helpers identify ordinary scalar-valued global sections, after forgetting
scalars, with maps from the unit sheaf, and then give a natural zeroth-global-RHom comparison.
The latter uses exact scalar forgetting and `rhom_global_sectionsOfUniverses`. An additive
universe lift accommodates the larger universe of derived morphisms. Transporting the cofan
along this comparison and reflecting colimits from additive groups to modules identifies the
colimit comparison definitionally with the displayed `DirectSum.toModule` map. No separate
claim of linearity of the auxiliary equivalence is necessary.

The final single-file `lcompile.py` check passed cleanly in 37.1 seconds. A textual check
confirmed that the theorem signature and public imports are unchanged.

Updated the existing node's proof, dependencies and proof origin to this route. Removed the
obsolete direct tool approvals for the closed monoidal and all-degree sections-model steps.
No definition, public declaration signature, or consumer was changed. No source-library file
was edited. The new direct proof imports are `RhomGlobalSectionsOfUniverses`,
`DerivedModuleDirectSums`, `RightDerivedFunctor.MapDerivedCategory`, `ModuleCat.Products`,
and `Grp.Ulift`.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.integralConstructible_hom_sums`
(node `lem-weil-pbc-integral-constructible-hom-sums`).

The item has zero remaining `sorry`s. Added zero holes and split off zero statements.
All three private helpers are proved. The proof uses the existing stated dependencies;
this report does not claim that their entire dependency closures are free of holes.

## No longer needed

Removed the direct proof imports `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
and `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`. The item's direct proof no longer
uses nodes `lem-sf-ringed-derived-closed-symmetric-monoidal` and
`lem-sfb-derived-internal-hom-sections-model`: shifting the targets first permits the existing
natural zeroth comparison instead. These modules still occur transitively in that comparison,
so no claim is made that they leave the library's import closure, and neither is withdrawn.

Removed the redundant direct import `Sheaf.Paper.AdicGlobalDerivedHom`, which is publicly
imported by `IntegralConstructibleBoundedBelowCompactness` and is still used through it.
No module is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement or source error was found. The previous route is longer than necessary: only
zeroth cohomology is needed after shifting the entire target family and coproduct. If the
original common lower bound is `n`, the shifted family has lower bound `n-q`. Shift preserves
the supplied colimit, and the final proof applies equally to empty families and negative `q`.

The generic existing nodes `lem-pur-rhom-global-sections` and
`lem-pc-derived-module-direct-sums` are used as homological-algebra tools; they do not replace
any step of the proper-base-change unit. Their modules are imported and their declarations
are actually used. The maintainer can record any additional tool approval required by the
unit checker. No new nodes or change records are needed.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
