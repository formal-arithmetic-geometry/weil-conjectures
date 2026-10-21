## What changed

Proved `SheafOfModules.ScalarPullback.action_existsUnique`, with its existing statement
unchanged. Convert the given universe-lifted presentations to the existing ordinary
algebraic inverse-image interface. Reuse the proved transported-action linearity helper
`CategoryTheory.FlatRingedDiagramInput.inverse_change_hom` from
`Sheaf.CategoryTheory.FlatRestrictionOrdinaryComparisons` through a private proof import.
The helper uses the two generalized graph equations on universal pairs to prove
additivity and scalar linearity; ring compatibility identifies the restricted scalar
actions. Faithfulness and reflection of isomorphisms by the underlying-sheaf functor
give an invertible natural comparison. The specified underlying formula determines it
uniquely. The conversion uses the existing `SheafOfModules.sheafUliftIso` helper from
`Sheaf.Paper.KFlatRingedToposPullback`; only a proved private reverse conversion is added.

The proof follows the restriction/action portion of the node's first step. Its node copy
now records the reused ordinary-comparison helper and its dependency. No public
signature or definition body changes, and the other three proofs retain their original
bodies. No source-library module is changed.

## Proved and sorry left

Closed one original hole:
`SheafOfModules.ScalarPullback.action_existsUnique`.

Three original holes remain, all attached to
`lem-sfb-kflat-scalar-comparison-normalization`:

- `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`.
- `SheafOfModules.ScalarPullback.θ_composition`.
- `SheafOfModules.ScalarPullback.θ_identity`.

Added zero holes. This is one proof, with no decomposition or split-off statement.
The action identification chosen in `a_h` now depends on a complete proof of existence
and uniqueness rather than a hole.

## No longer needed

Removed these direct private proof imports because the proved action argument does
not use them:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`.
- `Sheaf.CategoryTheory.GeometricModuleConstruction`.
- `Sheaf.Paper.RingedTopoiInverseImageTensorComparison`.

No DAG dependency or module is withdrawn: the remaining K-flat, derived-normalization,
and coherence proof plans still require their recorded dependencies. The unit route is
unchanged. `Sheaf.Paper.KFlatRingedToposPullback` remains privately imported for its
proved universe-lift comparison, with `import all` to access that private helper.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The existing ordinary transported-action
helper applies after explicitly removing the trivial universe lifts. Its hypotheses
require left exactness and the coefficient square, with no geometric right adjoint,
flatness assumption, boundedness restriction, or nonzero-ring assumption. Zero rings
and empty sites are therefore covered by the same proof.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
