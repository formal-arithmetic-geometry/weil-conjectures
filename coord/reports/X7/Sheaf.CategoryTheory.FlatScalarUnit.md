## What changed

Proved `SheafExactDegreeZero.scalarUniversal_of_flat` in
`Sheaf.CategoryTheory.FlatScalarUnit`, preserving its complete signature and docstring.
The ordinary extension functor is the concrete sheafified sectionwise extension.
Private proved helpers identify its restriction with tensoring by the coefficient sheaf,
prove preservation of K-flat quasi-isomorphisms, and check the ordinary and derived
single-complex unit squares. The existing K-flat transpose theorem then computes
extension on the flat source. The ordinary Hom bijections identify the prescribed
recipient with scalar extension by an isomorphism, which supplies the asserted
bijections for all unbounded derived test objects.

The proof imports `ExactRightDerivedAdjointKFlatRepresentative` for the normalized
K-flat transpose, the source `DerivedCategory.KFlatAcyclic` and
`DerivedCategory.Adjunction` modules for derivation, Mathlib
`CategoryTheory.Adjunction.Additive` for additivity of the ordinary left adjoint,
and the source `GrothendieckAbelian.HasColimitsOfShape` for the countable sheaf
coproduct instance used by the K-flat machinery.

Only proof imports and private proved helpers were added. No public definition,
statement, attribute, or public import changed. Updated the item's DAG proof to
record this route. No other module needs adaptation.

## Proved and sorry left

Closed the one original hole in
`SheafExactDegreeZero.scalarUniversal_of_flat`
(node `lem-asd-flat-ordinary-scalar-unit-derived`).
Added zero holes and zero split-off statements. The delivered module contains zero
`sorry`s. Imported declarations retain their existing upstream proof dependencies.

Validation: the delivered module compiles without warnings through `lcompile.py`
against the server build in 10.9 seconds. Import-direction checks pass for all
three new Sheaf/source proof imports. The public signature and docstring were
compared with the assigned source and are unchanged.

## No longer needed

The proof does not use `lem-pur-derived-change-of-rings` or its recorded module
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, whose ringed-site presentation
would require transporting this theorem to a different module-sheaf category.
It directly derives the concrete scalar-extension adjunction instead.

The proof does not use `lem-pc-bounded-above-flat-kflat-site` or its module
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`: the source library's direct
single-complex criterion supplies K-flatness from the given flatness hypothesis.
The independent-coefficient K-flat interface module
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients` is not imported; the adopted
categorical K-flat predicate is already available for the original category.
The mathematical K-flat dependency is retained in the node.

No pre-existing import was removed, and no module was withdrawn. These dependency
omissions concern this proof only; other consumers can still need those modules.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-site dependency declarations use `SheafOfModules`, whereas this
item uses `Sheaf J (ModuleCat R)`. Transport between them is unnecessary: sheafified
ordinary extension, the monoidal sheafification comparison, and the existing
categorical K-flat derivation machinery work directly in the stated category.
No mathematical statement was changed. The unit's route is preserved.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
