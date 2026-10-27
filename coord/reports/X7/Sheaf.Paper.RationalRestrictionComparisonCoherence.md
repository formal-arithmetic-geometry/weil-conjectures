## What changed

Partially proved `Sheaf.Paper.RationalRestrictionComparisonCoherence`. The unit comparison is
transported from the localized integral isomorphism using the pullback object formula. The
canonical scalar comparison hom components follow from the published normalizations; their
inverse components follow from uniqueness of an isomorphism with a given hom. Pullback and
tensor pure-arrow actions follow from the published operation specifications. The equation
calculus applies those formulas at coefficient one and uses functorial preservation of
equality, identities and composition.

All 32 existing public signatures and all existing definition bodies are unchanged. Local
irreducibility annotations keep elaboration from expanding derived operations and localized
Hom module instances. The retained earlier full draft and diagnostics remain in `scratchpad`;
they are not part of the delivery.

## Proved and sorry left

Closed four of the eight original holes:

- `unitComparison_existsUnique`
- `scalarComparisons_localized`
- `pureArrowActions`
- `equationCalculus`

Four original holes remain, all attached to
`lem-pur-rational-restriction-comparison-coherence`, with their original proof docstrings:

- `tensorComparison_existsUnique`
- `mixedSquares`
- `identityCoherence`
- `towerCoherence`

Added zero holes and zero split-off statements. The proofs use the existing declared operation
specifications; their imported holes remain in their own modules.

## No longer needed

Removed the private imports `Sheaf.CategoryTheory.SemilinearScalarLocalization` and
`Sheaf.Paper.IntegralOperationsScalarComparisons`. The completed proofs use the published
rational operation and comparison specifications rather than reconstructing their localization.
The direct proof dependency `lem-pur-semilinear-scalar-localization` is removed from this node's
route. No module or declaration is withdrawn. Integral operation comparison and scalar
composition dependencies remain necessary for the unfinished coherence arguments.

## Where the brief, the DAG or earlier work was wrong

The previous full draft did not compile and its lack of textual `sorry` was not a proof.
This delivery includes only validated proof bodies and restores the other four original holes.
The old infrastructure space failure is no longer present.

The DAG's original step 7 describes integral compatibility as supplied directly. The current
interface states ordinary compatibility and defines completed comparisons by conjugation.
Identity and tower proofs must still perform that conjugation and identify its completion
comparison with the normalization of the integral scalar unitor and associator. The revised
node records that argument as the remaining plan, without claiming it has been formalized.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
