## What changed

In `Sheaf.Paper.FiniteDerivedComparisonNormalization`, proved
`CategoryTheory.FiniteDerivedComparison.finiteDerivedComparisonNormalization`
by the existing tensor-comparison descent theorem. Private, fully proved helpers
show resolving pullback/tensor closure, existence of resolving replacements,
full faithfulness of restriction, restriction of the supplied site tensor model,
and naturality of the uncurried ordinary comparison. The actual cochain counit
computes pullback on resolving complexes, so the descended square is exactly the
existing `Normalized` predicate. Uniqueness is inherited by cancelling the same
representative square, with proof irrelevance for the resolving witnesses.

Proved `CategoryTheory.FiniteDerivedComparison.coefficientComparison_identity_successive`
by specializing the existing finite-word descent evaluation to identity and
vertical composition expressions. Existing public signatures and definitions
are unchanged. All new proof dependencies are private imports. The existing node
records the implemented descent route and the retained plans of the other clauses.

## Proved and sorry left

Original holes: 5. Closed: 2. Added: 0. Split off: 0.

Closed:
- `CategoryTheory.FiniteDerivedComparison.finiteDerivedComparisonNormalization`.
- `CategoryTheory.FiniteDerivedComparison.coefficientComparison_identity_successive`.

Remaining, unchanged named statements, all attached to
`lem-pur-finite-derived-comparison-normalization`:
- `CategoryTheory.FiniteDerivedComparison.tensorComparison_coherence`.
- `CategoryTheory.FiniteDerivedComparison.tensorComparison_composition`.
- `CategoryTheory.FiniteDerivedComparison.tensorComparison_coefficients`.

This is a partial proof delivery, not a claim that the whole normalization node
or its three remaining coherence clauses is proved.

## No longer needed

Removed private imports:
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.

The first completed theorem uses representative descent directly, rather than
constructing the published shift/unit comparison and identifying it afterwards.
The word identity and composition equations use only finite-word descent.
The removed modules are still in the proof plans for the three unclosed clauses;
no module withdrawal or global pruning is requested. The node retains those
needed dependencies. No unit-level route is bypassed and no source declaration
is removed.

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement was found. The first proof plan can be made
shorter using the already proved representative-descent and restriction lemmas.
The final identity/successive clause is exactly an existing finite-word descent
specialization and does not require a second tensor-descent argument.

An explored coherence route needs an explicit adapter between
`CochainTensorComparison.CanonicalRingedTensorComparison` and
`SheafOfModules.CanonicalRingedTensorComparison`, and between their selected
chain/derived comparison maps. Their fields agree, but they are distinct public
structures. The private adapter exploration is excluded from this packet; it
introduced no delivered declarations or holes.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
