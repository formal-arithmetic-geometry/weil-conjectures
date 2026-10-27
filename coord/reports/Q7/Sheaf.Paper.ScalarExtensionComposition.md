## What changed

Completed the nine existing proofs in `Sheaf.Paper.ScalarExtensionComposition`, preserving
all existing public signatures and definitions. The ordinary sheaf associator and unit are
constructed by conjugating the normalized scalar-extension adjunction with composition and
identity of scalar restriction. Their normalization and uniqueness follow from tensor
generators. Exact-functor derived comparisons, restriction to the full integral subcategories,
and raw Hom scalar localization give the derived and rational comparisons. Generator equations
prove both unit laws and the pentagon. Conjugating by the existing normalized completion
comparison gives the laws for the published completed functors and their existential family.
All added helpers are private and proved. The full module compiled successfully in 53.1 seconds;
the development profiler option and checkpoints were then removed before delivery.
Sequential elaboration keeps proof checking and linting within the standard limit. Generic ring-sheaf lemmas avoid repeated
unfolding of completed coefficient and localization constructions. Proof-scope commands and
all downstream consumers are recorded in
`coord/changes/Q7-scalar-extension-composition-proof-context.md`. Updated the owning node's proof route to include
the preserved legacy interface without changing the intrinsic interface attachment.

## Proved and sorry left

Closed all nine existing holes, with no holes added or split off:

- `WeilConjectures.exists_rationalScalarExtension_composition`
- `WeilConjectures.integralOrdinaryScalarComp_existsUnique`
- `WeilConjectures.integralOrdinaryScalarUnit_existsUnique`
- `WeilConjectures.integralConstructibleScalarComp_existsUnique`
- `WeilConjectures.integralConstructibleScalarUnit_existsUnique`
- `WeilConjectures.rationalOrdinaryScalarComp_existsUnique`
- `WeilConjectures.rationalOrdinaryScalarUnit_existsUnique`
- `WeilConjectures.rationalOrdinaryScalar_coherence`
- `WeilConjectures.rationalConstructibleScalar_coherence`

No `sorry` remains in the delivered module. Existing imported theorem assumptions remain
with their owning modules; no declaration or assumption is replaced or weakened.

## No longer needed

Removed the five original private proof imports:

- `Sheaf.Paper.DerivedCompleteIntegralDetailed`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`

The legacy proof does not directly use `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`, or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: exactness of the already defined ordinary
scalar functor permits the existing canonical exact-functor derived localization API instead.
Tensor and completion definitions remain available through the preserved public import
`Sheaf.Paper.RationalizationKaroubi`. The owning node still needs its existing intrinsic
comparison dependencies for `SfScalarExtensionComposition`; those are preserved. No library
module is withdrawn, and no existing source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The active node attachment belongs to `SfScalarExtensionComposition`; this item is its preserved
legacy dependency and still contains nine proof holes. Its ordinary tensor comparisons are
used by the active intrinsic interface, so the absence of a current primary Lean attachment
is not grounds to withdraw it. The pre-existing sandbox attempt needed universe and
transparency repairs against the current compiler. Public statements remain unchanged.

The latest blueprint no longer contains the old `sk-def-sf-operations` path recorded in the
historical node source. The current `sk-def-sp-scalar-extension` composition paragraph and
its proof step (4) give the same balanced tensor associativity and unit/pentagon argument;
`sk-lem-sp-tower/lem-coef-integral-finite-extension.proof.md` uses this associator explicitly.
The unit's statement and route are preserved, and no new nodes are introduced.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
