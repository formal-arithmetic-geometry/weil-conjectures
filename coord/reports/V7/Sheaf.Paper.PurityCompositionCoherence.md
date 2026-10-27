## What changed

Partial proof delivery for `Sheaf.Paper.PurityCompositionCoherence`.
All existing declaration signatures, definitions, public imports, and visibility are retained.

The zero and successor coefficient-power equations follow by reflexivity.
The three tensor/pullback normalizations and the associator normalization use the specified
canonical isomorphism as witness and heterogeneous equality for uniqueness. Finite lifted
coefficients use Mathlib's `isNoetherian_of_finite`. The source-normalization proof constructs
all eight prescribed factors with their explicit adjacent types, composes them, and uses the
eight equality clauses to identify every other normalized source isomorphism with that composite.

`compositionExceptional_ctf` applies `smooth_exceptional_preservation`, compares the two
exceptional presentations by `Functor.mapDerivedCategoryCompIso`, and transports membership
using the proved isomorphism-closure clause of `finite_ctf_isTriangulated`.
`compositionInput_bounded` converts finite homological support to an ordered integer interval,
applies `finiteRing_constructibleDerived_origin`, converts the etale constructibility and
boundedness predicates, then transports its witness through the realization equivalence.
No representative or orientation is chosen as new definition data.

Three private proof imports are added:

- `Sheaf.Paper.FiniteCtfTriangulated`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`

The unused-section-variable linter is disabled for `compositionInput_bounded` alone to retain
its existing finite-type-base hypotheses verbatim. No hypotheses are removed.
The eight normalization proofs compiled together in 27.0 seconds. The ten-proof version after
removing the private imports compiled in 15.7 seconds; final warning-free validation follows
through `lcompile.py` and the delivery gate.

Edge cases: all constructions retain degree zero, arbitrary (including zero) finite rings,
empty schemes, and zero complexes. The bounded-support conversion uses `min` and `max`, so
it does not assume the nonzero homology support is nonempty. No smoothness is added to the
unresolved general exceptional-composition theorem.

## Proved and sorry left

Closed 10 of the 12 original direct holes, with no new holes and no split-off statements.
All names below have prefix `WeilConjectures.PurityFiniteSetting.`

- `compositionEtalePowerZero`.
- `compositionEtalePowerSuccessor`.
- `existsUnique_compositionPullbackTensor`.
- `compositionCoefficientNoetherian`.
- `existsUnique_compositionPullbackTensorFixed`.
- `existsUnique_compositionFixedPullbackComp`.
- `existsUnique_compositionTensorAssociatorFixed`.
- `existsUnique_compositionSourceFixed`.
- `compositionExceptional_ctf`.
- `compositionInput_bounded`.

The two original named public theorem holes remain unchanged, both attached to
`thm-pur-composition-coherence`:

- `isIso_compositionExceptionalMap`.
- `smoothPurityCompositionCoherence`.

This is a partial proof delivery permitted by the brief's several-sorry rule. It does not
claim the final coherence theorem or the entire target closure is proved. Existing imported
statements may still depend on their own named holes; none is introduced by this delivery.

## No longer needed

Removed these 17 unused private proof imports from this module:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`.
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`.
- `Sheaf.Paper.CartesianCoefficientTwists`.
- `Sheaf.Paper.CohomologicalSmoothComposition`.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.PurTwistSheafLocallyFree`.
- `Sheaf.Paper.PurityDiagonalDualizingObject`.
- `Sheaf.Paper.PurityDiagonalSectionPasting`.
- `Sheaf.Paper.PurityDncComparisons`.
- `Sheaf.Paper.VectorBundlePurity`.

These imports are unnecessary for the completed auxiliary proofs and existing constructions.
Some of their definitions remain available through the unchanged public imports. No global
module withdrawal or DAG-node pruning is claimed: the two unresolved statements retain their
original dependency plan, including the tensor-mate, compatible-chart, and orientation-descent
nodes. No source-library declaration is removed. The proof route of the unresolved main
statement and the unit's route are unchanged, so no node copy is edited in this proof delivery.

## Where the brief, the DAG or earlier work was wrong

The declared main-theorem proof dependency `lem-pur-composition-model-orientation-descent`
is attached to `Sheaf.Paper.CompositionModelOrientationDescent`, which publicly imports this
item. The prescribed import is currently cyclic. Checked with
`tools/import_direction.py may Sheaf.Paper.PurityCompositionCoherence
Sheaf.Paper.CompositionModelOrientationDescent`: the tool reports that the imported module
already reaches this item. A later completion must separate the shared canonical comparisons
from the final theorem, or supply the needed orientation interface without this cycle.
This delivery retains the comparisons and leaves the main theorem's statement unchanged.

The theorem `isIso_compositionExceptionalMap` applies to arbitrary separated finite-type
morphisms; `composition_tensor_mate` requires smooth morphisms. Its smooth specialization
cannot discharge that general theorem by itself.

Searches actually run with `msearch.py`: leanfinder for smooth purity map compatibility with
composition (eight results about smooth composition, no purity-coherence theorem); loogle
`IsNoetherianRing, Finite` (12 results, none the desired finite-module instance); grep
`composition.*[Pp]urity|[Pp]urity.*[Cc]omposition` (zero hits). Local source search found the
existing Mathlib `isNoetherian_of_finite` instance and the finite-ring derived-origin and
smooth exceptional-preservation declarations used here. The latest blueprint composition
statement, proof, and smooth-purity/composition unit records were read. No new node is needed.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
