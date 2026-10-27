## What changed

Changed only the proof bodies, proof docstrings and private imports of
`Sheaf.Paper.PodReindexingHomCoefficientDescent`; every existing public signature,
definition body and public import is preserved. Added proved private helpers for the unique equality transport of an
isomorphism and for the underlying object of an inherited subcategory shift.

The ambient scalar comparison and its unit/tower equations reuse the existing
integral-operation scalar interface. Shift stability and fullness restrict the
original signed ambient Hom isomorphism. Completed-evaluation reflection and its invertible ordinary-to-completed maps
give the integral permitted-pair assertion; the recorded rational pullback
object formula then gives the rational assertion.
Naturality follows directly from the normalized natural isomorphism. The common
tensor map is its existing map transported along the recorded object equalities,
and the common signed-shift equation is the image of the rational equation.

Updated the item's existing node proof, proof dependencies and proof origin to
record these arguments. No new modules, declarations with holes, definition
repairs, forced adaptations or withdrawals are included.

## Proved and sorry left

Closed 9 of the original 32 holes; added 0; split off 0.
All names below have namespace `WeilConjectures.PodCoefficientDescent` and node
`lem-pod-reindexing-hom-coefficient-descent`.

Closed:

- `ambient_scalar`
- `ambient_tower_unit`
- `shifted_pair_permitted`
- `integral_signedShift_existsUnique`
- `rational_pair_permitted`
- `rational_naturality`
- `integral_pair_permitted`
- `common_tensorComparison_existsUnique`
- `common_signedShift_images`

The following 23 existing named theorem holes remain unchanged:

- `ambient_reindex_scalar`
- `ambient_scalar_chain`
- `ambient_coordinates`
- `rational_transpose_existsUnique`
- `rational_signedShift_existsUnique`
- `integral_comparison_existsUnique`
- `rational_comparison_existsUnique`
- `integral_existsUnique`
- `integral_scalar`
- `rational_scalar`
- `integral_evaluation_transposition`
- `rational_evaluation_transposition`
- `rational_composition`
- `rational_pullbackShift_existsUnique`
- `rational_signed_shifts`
- `common_evaluation_existsUnique`
- `common_pair_permitted`
- `common_comparison_existsUnique`
- `common_evaluation`
- `common_transpose_existsUnique`
- `common_transposition`
- `common_compositor_existsUnique`
- `common_composition`

The closed theorems are proved from existing library interfaces, some of which
still contain their separately recorded holes. This packet does not claim those
dependencies are axiom-free. The remaining item theorems retain their existing
source references and complete proof plans in their docstrings and DAG node.

## No longer needed

Removed these unused private imports:

- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange`
- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor`
- `Sheaf.Paper.IsomorphismScalarTensorKFlatModel`
- `Sheaf.Algebra.Homology.ScalarHomTensorCoherence`
- `Sheaf.Algebra.Homology.ScalarHomComparisonTower`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.PrincipalKoszulStrictReplacement`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange`
- `Sheaf.Paper.IntegralAmbientOperationModels`
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`
- `Sheaf.Paper.SpecifiedPullbackComparisonAlpha`
- `Sheaf.Paper.IsomorphismComparisonScalarExtension`

The shortened ordinary unit/tower proof no longer needs
`lem-sfb-scalar-hom-tensor-coherence` or
`lem-pur-scalar-hom-comparison-tower`; these are removed from this node's
`proof_deps` and obsolete top-level `tool_uses` approvals. Their modules are not withdrawn: other items may still need them.
The other removed imports belong to arguments for the remaining holes or are
already available through preserved public interfaces. Their still-needed plan
dependencies remain in the DAG. No public import is removed, and no claim is made
that an upstream source declaration can be removed.

## Where the brief, the DAG or earlier work was wrong

The planned first step reproved an ambient scalar-isomorphism assertion already
present as `scalarHomOrdinary_isIso`. Likewise, the unit/tower step duplicated
the third clauses of `scalarOperationsOrdinary_unit` and
`scalarOperationsOrdinary_tower`. Those interfaces have exactly the required
normalizations, so they provide a shorter proof route. Naturality of an already
constructed rational natural isomorphism needs no new pure-tensor calculation.
No false statement, target change or unusable dependency was found.

Validation: the complete module compiled successfully through `lcompile.py`.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
