## What changed

Proved `CategoryTheory.constantModule_section_properties` in
`Sheaf.Paper.ConstantModuleSectionProperties`, with its statement unchanged.
All auxiliary constructions and lemmas are private to the module. The three instance
properties are private theorems registered only as local instances.
The constant-section functor preserves finite limits; a set-theoretic section,
transported through `constantCommuteCompose`, proves sectionwise surjectivity.
The canonical tensor map is constructed from the functor's linear action on morphisms.
An explicit coordinate inverse proves the finite free case. A finite presentation,
tensor right exactness and an explicit right-exact diagram chase prove bijectivity.
Tensor induction proves restriction naturality. The ideal tensor criterion then
proves flatness. The empty finite presentation and zero modules are covered by the
same finite-sum identities; no nonempty-site hypothesis is used.

Added proof imports of `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`,
`Mathlib.CategoryTheory.Linear.FunctorCategory`, and
`Mathlib.CategoryTheory.Linear.LinearFunctor`. Existing public imports are unchanged.
Updated the item's DAG proof to match these constructions and the dependency pruning.
No existing definitions, statements, consumers or target signatures were changed.
The proof-scope command changes are recorded in
`coord/changes/constant-module-section-properties-proof-scope.md`, including all
11 downstream importers and their holders. No consumer adaptation is needed.

Validation: the final module compiled cleanly through `lcompile.py` in 8.7 seconds.
The delivery dry run passed, including the axiom audit and static preflight.
The unchanged direct importer `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`
also compiled in 6.0 seconds against the changed module in a scratch overlay;
the changed module compiled in 10.9 seconds in that overlay. Searches through LeanFinder, Loogle,
the source library and Mathlib found no existing theorem providing all three clauses.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.constantModule_section_properties`
(node `lem-weil-pbc-constant-module-section-properties`).
Added 0 holes. No `sorry` remains in this module or is introduced elsewhere.
This is a proof, not a decomposition; no split-offs or new modules are needed.

## No longer needed

Removed the proof import `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
The dependency `lem-pc-sites-module-sheafification-interface` is unnecessary:
Mathlib's module-valued sheafification already preserves finite limits directly,
and `constantCommuteCompose` supplies the comparison with sheaves of sets.
The varying-ring module-sheafification interface is never used.
All other declared proof dependencies remain used. No project module is withdrawn.
The provisional explicit import of
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` was also removed because
`ExactFunctor` supplies the needed categorical exactness API.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and source proof are correct. The DAG's citation of the
varying-ring module-sheafification interface was redundant for this fixed-ring
`ModuleCat` theorem. The formal proof works directly with module-valued sheafification.
The tensor comparison needs an explicit proof that the section functor is R-linear;
this is proved from naturality and uniqueness of sheafification.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
