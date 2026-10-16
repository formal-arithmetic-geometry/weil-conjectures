## What changed

Proved `exists_rightDerived_computes_acyclic_of_finite_dimension` by taking the existing
unbounded right derived functor, constructing its comparison through the homotopy-category
factorization and quotient isomorphisms, and using the right-derived universal property.
The comparison is shown invertible on right-acyclic complexes by the finite-dimensionality
lemma, and its naturality supplies the chain-map square. The finite-dimensionality API is a
private proof import.

## Proved and sorry left

Closed the sole sorry, `exists_rightDerived_computes_acyclic_of_finite_dimension`.
No sorry remains in this module and no new sorry was added.

## No longer needed

Removed the proof-only imports `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`,
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`,
`Sheaf.CategoryTheory.KInjectiveTotalDerived`, and
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.
The finite-dimensionality API transitively supplies the required construction and
universal-property declarations; all three public imports remain needed by the theorem's
exposed statement.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expands the construction through injective resolutions and long exact
sequences. The library already contains that construction and its finite-dimensionality
comparison theorem in `DerivedCategory.FiniteCohomologicalDimension`, so the target reduces
to assembling the universal property and quotient factorization maps.

## Second reading by H1

1. Compared the sandbox module with the repository version: the theorem signature and all existing declarations are byte-for-byte unchanged; only the proof, one private import, and this report were changed.
2. Compiled the module with `lcompile.py`; it has no errors, warnings, `sorry`, forbidden declarations, or hollow definitions. A scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. Checked the proof against the existing finite-cohomological-dimension API and Mathlib right-derived universal property. The construction uses the canonical quotient comparison, `rightDerivedDesc`, and `rightDerived_ext`; no duplicate split-off theorem or new node was introduced.
4. The proof takes the shorter existing-library route through `DerivedCategory.FiniteCohomologicalDimension`; the four unused proof-only imports were removed and the public statement imports were retained.
5. The target node statement is unchanged and the unit route is preserved; no new sorry or dependency node is added.

Changed after review: pruned the four unused private imports and updated this report.
