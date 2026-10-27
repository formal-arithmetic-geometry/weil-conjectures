## What changed

Partial proof delivery in `Sheaf.Paper.DerivedAutomorphismHomEvaluation`, preserving all
existing public declarations, signatures, definitions and public imports.

The completed ring lift is identified with the existing projection-normalized
`isoReductionCompletedMap`; this proves projection naturality and invertibility.
The existing exact sectionwise module equivalence induces the completed derived
inverse-image equivalence. The completed integral closed structure is constructed
from the proved completion-unit Hom bijection, additive ordinary transposition and
full-subcategory Hom equivalences; naturality and the stated normalization give
existence and uniqueness. The two constructible shift isomorphisms lift the stated
ambient composites through the fully faithful inclusion. The finite argument-first
evaluation and transpose equations follow from the existing Hom-first laws and the
canonical tensor-pullback braiding square.

Two private proved helpers supply additive ordinary transposition and extensionality
of the partial closed structure. Proof imports add `Mathlib.CategoryTheory.Adjunction.Additive`
and `import all Sheaf.Paper.IsomorphismReductionTower`, reusing its existing proved
private module-equivalence helper, as already done by `PodReindexingStrictComparisons`.
The completed ring lift is locally irreducible after its projection proof, so later
instance checks use its established interface rather than unfold its limit cone.
The three overlapping `isoReduction*` sheafification/smallness instances are disabled
locally to avoid unresolved universe constraints. The main DAG node retains its six-step
plan for the remaining companions and records the proofs now implemented.

Validation: the module compiled on the server with all eight proofs present.
The delivery command repeats compilation and runs the project preflight checks.

## Proved and sorry left

Closed 8 of the original 36 holes, with no new holes or split-off statements:

- `WeilConjectures.podIntegralClosed_existsUnique`.
- `WeilConjectures.podCompletedRingProjection_naturality`.
- `WeilConjectures.podCompletedRingMap_isIso`.
- `WeilConjectures.podCompletedInverseImage_equivalence`.
- `WeilConjectures.podArgumentFirst_finite`.
- `WeilConjectures.podArgumentFirst_finite_transpose`.
- `WeilConjectures.podIntegralHomShift_existsUnique`.
- `WeilConjectures.podIntegralPullbackShift_existsUnique`.

The following 28 holes remain unchanged. Each belongs to
`lem-pod-derived-automorphism-hom-evaluation` and retains its existing source and
natural-language proof docstring:

- `WeilConjectures.podFiniteHomComparison_laws`.
- `WeilConjectures.podIntegralHomComparison_laws`.
- `WeilConjectures.podRationalClosed_existsUnique`.
- `WeilConjectures.podRationalHomComparison_laws`.
- `WeilConjectures.podCommonClosed_existsUnique`.
- `WeilConjectures.podCommonHomComparison_laws`.
- `WeilConjectures.podSystemHomComparison_laws`.
- `WeilConjectures.podFiniteRestrictionOrdinary_existsUnique`.
- `WeilConjectures.podOrdinaryLimitReindexing_existsUnique`.
- `WeilConjectures.podLimitReindexing_existsUnique`.
- `WeilConjectures.podReductionReindexingMap_laws`.
- `WeilConjectures.podCompletedToTower_laws`.
- `WeilConjectures.podHomReductionSquare`.
- `WeilConjectures.podHomComplexShift_existsUnique`.
- `WeilConjectures.podDerivedHomShift_existsUnique`.
- `WeilConjectures.podFiniteHomComparison_shift`.
- `WeilConjectures.podFiniteHomComparison_comp`.
- `WeilConjectures.podIntegralReindexedHom_shift`.
- `WeilConjectures.podCompletedModuleComp_existsUnique`.
- `WeilConjectures.podIntegralPullbackComp_normalization`.
- `WeilConjectures.podIntegralHomComparison_comp`.
- `WeilConjectures.podSystemNormalized`.
- `WeilConjectures.podSystemHomComparison_fiber`.
- `WeilConjectures.podArgumentFirst_integral_rational`.
- `WeilConjectures.podArgumentFirst_common`.
- `WeilConjectures.podRationalHomComparison_comp`.
- `WeilConjectures.podCommonHomComparison_comp`.
- `WeilConjectures.podIntegralRationalHomComparison_shift`.

## No longer needed

Removed these redundant direct proof imports, each already publicly imported
by a retained dependency:

- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`.

No mathematical node or module is withdrawn. In particular, all six declared
proof dependencies remain in the plan for the unfinished companion theorems.
No source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The declared system-square dependency `Sheaf.Paper.ReindexingSystemHomReductionSquare`
publicly imports this item. Importing it here to discharge `podHomReductionSquare`
would form a cycle. Its mathematical statement remains needed; this delivery leaves
that hole unchanged and does not claim to prune the dependency. The shared interface
would need extracting before that direction of use can be implemented.

The original docstrings refer to sixteen proof steps, while the current DAG has six
grouped steps. This delivery preserves the statements and interprets those references
as the original detailed plan.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
