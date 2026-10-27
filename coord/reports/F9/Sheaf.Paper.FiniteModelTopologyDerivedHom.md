## What changed

Closed the proofs of `homComparison_naturality`, `globalComparison_naturality`, and
`sectionRingComparisons` in `Sheaf.Paper.FiniteModelTopologyDerivedHom`. The proof uses the
specified scalar adjunction, evaluation transpose, derived sections naturality, and the
section-ring comparison. Exploratory bridge statements were not included in the delivery.

## Proved and sorry left

Proved: `homComparison_naturality`, `globalComparison_naturality`, and
`sectionRingComparisons` (3 of the 6 original holes). The remaining original holes are
`finiteModelTopologyDerivedHom`, `scalarExtendedEvaluation`, and
`finiteCoefficientComparison_sections`; each remains as its original named theorem with
`by sorry`. No new `sorry` declarations were added.

## No longer needed

Removed unused private imports:
`Sheaf.Paper.AdicConstructibilityPredicateComparison`,
`Sheaf.Paper.ConstructibleInternalHomContinuity`,
`Sheaf.CategoryTheory.DerivedSectionsScalarCoherence`,
`Sheaf.CategoryTheory.InternalSectionTensorComparison`,
`Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`,
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
The remaining unproved main theorem still has the original DAG plan, so no node is declared
unnecessary. The exploratory scratch modules were removed from the Lean source before delivery.

## Where the brief, the DAG or earlier work was wrong

The existing declarations expose the scalar composition and topology comparison objects,
but do not provide the normalization equalities needed to identify the prescribed native
maps with the generic norm and global comparison theorems. The remaining three holes require
those independent normalization arguments; the three naturality and section-ring statements
are provable directly from the exposed adjunction and comparison APIs.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
