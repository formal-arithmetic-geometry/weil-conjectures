## What changed

Completed `SheafOfModules.DerivedQuotientTower.exists_presentation`, preserving its
statement and all three existing constructions. Private proved helpers build the
ordinary extension functors, strict transition maps, and the scalar-unit augmentation.
The transitions extend the balanced maps on presheaf tensors through the locally
bijective sheafification unit. Equality is checked on local pure tensors.

Levelwise K-flat invariance uses the independent-coefficient version already proved
in `DerivedChangeOfRingsIndependentCoefficients`. Exact faithful forgetting to
abelian sheaves handles restriction of scalars. Componentwise quasi-isomorphism
detection handles strict towers. The resolving-class theorem then gives the universal
homotopy-category counit, and its lift/factorization/extensionality API proves the
stated unique-lift property. The resolution clause is the existing K-flat resolution
theorem with its unused flat-term and epimorphism conclusions discarded.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.DerivedQuotientTower.exists_presentation`
(node `lem-weil-pbc-derived-quotient-tower-presentation`).
No holes added or split off. No `sorry` remains in the delivered module.
The module compiled successfully through `lcompile.py` (24.9 seconds); its original
public signature, definitions, and public imports are unchanged.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`.
Its mathematical K-flat invariance step is retained using the existing proved
independent-coefficient implementation. The direct DAG dependency is accordingly
changed from `lem-pur-change-of-rings-kflat-quasi-iso` to the existing
`lem-pur-derived-change-of-rings` implementation containing that helper.
No mathematical node or module is withdrawn. The unused experimental proof import
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` was also removed.
All existing public imports are retained; the proof adds only private proof imports.

## Where the brief, the DAG or earlier work was wrong

The recorded `changeOfRings_kFlat_quasiIso` specialization identifies the site object,
site morphism, and coefficient universes. It cannot be applied directly to this
statement's independent universes. The already proved private theorem
`derivedChangeOfRingsIndependentCoefficients_kflat_invariance` supplies exactly the
needed generality, without changing any hypothesis or conclusion.
The unit route and all five mathematical proof steps are preserved.

The item node now records the actual Step 3 implementation and its dependency.
No statements, definitions, source-library declarations, or consumer modules change.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
