## What changed

Prove the six clauses of `section_derived_tensor_normalization` from the stated
K-flat comparison and actual representative-square declarations. The proof first
identifies the actual conjugated tensor isomorphism on resolving representatives,
then cancels equivalence comparisons to obtain both tensor squares. It derives
the unit equation from the representative unit equation. The existing generic
monoidal and oplax-square constructions supply the constraint equations.

Every existing public declaration signature is preserved. The regular-unit and
section-unit definitions now use the existing total-complex unit interfaces;
unfolding those interfaces recovers the original composites by functoriality.
This avoids repeatedly elaborating the large concrete category structures.
The additional categorical lemmas are private and proved in the item module.

The proof imports the declared K-flat comparison and actual representative-square
modules, the generic derived monoidal API, and the generic oplax-square API.
`import all Sheaf.Paper.ProEtaleSectionModuleFunctors` gives access to its existing
proved private equality between the mate and canonical ordinary structures.
The existing projection instance caches from `IntegralResidueDerivedMonoidal`
are used only locally. `SectionTotalOplaxComparisonData` is a public import because
its real unit constructions now occur in public definition bodies.

Definition and consumer review is recorded in
`coord/changes/Y7-section-derived-tensor-unit-api.md`. The downstream scan finds
28 transitive consumers, and no external textual use of either changed helper.
No consumer adaptation, new statement, new node, or hollow definition is added.

## Proved and sorry left

The original hole is
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.section_derived_tensor_normalization`.
The complete proof closes this one hole and adds zero holes and zero split
statements. No `sorry` remains in the item module. The final complete proof
compiled together with the delivery axiom audit in 42.0 seconds, without warnings.
Factoring the repeated ordinary monoidal equality into proved private lemmas
keeps the concrete derived comparison proofs compact. The expensive component conversion is
performed using its generic conjugation equation, rather than rewriting through
the concrete derived category. Existing imported stated dependencies retain their
own proof obligations; none is duplicated here.
The original and compact unit formulas were separately proved equal in a clean
29.0-second compile.

## No longer needed

The proof does not directly use the following original proof imports:

- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Sheaf.CategoryTheory.SheafTensor`
- `Sheaf.Algebra.Homology.KFlatModuleObject`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.DerivedPullbackRepresentativeComputation`
- `Sheaf.Paper.TensorPullbackRepresentativeDescent`

Below this item the separate direct uses of
`lem-pd-section-oplax-total-comparison`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-kflat-tensor-pullback-computation-universes`,
`lem-weil-pbc-tensor-comparison-descent-representatives`, and
`lem-weil-pbc-localization-universal-property` are unnecessary: the stated actual
representative square and the injectivity supplied by site tensor descent give
the required identification. Their use by other nodes and by retained public
definitions is unaffected. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The old plan repeated representative computations
already available in its declared dependencies. Generic oplax transport gives a
shorter proof of the final three constraint equations.

The ordinary internal pullback carries both a mate monoidal structure and the
canonical scalar-extension structure. The proof uses the existing proved
equality between them; it does not assume they are definitionally identical.
The generic derived monoidal API is recorded by the existing node
`new-proetale-derived-module-pullback-monoidal`. The oplax-square API is recorded
by `lem-sfb-oplax-monoidal-of-lax-square`. Both are generic categorical tools in
this proof; the dependency update makes their use explicit for review.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
