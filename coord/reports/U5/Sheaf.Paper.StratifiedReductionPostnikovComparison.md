## What changed

In `Sheaf.Paper.StratifiedReductionPostnikovComparison`, filled four of the seven
original theorem holes, preserving every public declaration signature and definition.
Added the proved private helper `spStratifiedScalarFinite` before the completed-ring
comparison, so its finiteness proof can be reused without changing declaration order.

The scalar quotient maps form a natural cone by `NatTrans.ofOpSequence`; faithful
forgetting recovers the stipulated preimages. The finite restriction comparisons
are natural by the existing constant-ring inverse-image naturality theorem.
Cofinality of uniformizer and ell powers exhibits every scalar quotient as a
surjective image of a finite uniformizer quotient. Finally the completed-ring map
is the cone-point isomorphism obtained from preservation of this finite constant-ring
tower limit: the defining projections identify its hom with the actual limit lift.

Added proof imports of `Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerLimit`,
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage` and
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`. Updated the existing node's
proof, proof dependencies and proof origin with this completed coefficient step;
the remaining six steps are retained as the plan for the open proofs.

The complete module compiled through lcompile.py after import cleanup, with exit
code 0, no warnings, in 26.3 seconds of server compiler time. This is a partial
proof delivery allowed by the multiple-sorry rule, not a decomposition.

## Proved and sorry left

Closed four original holes (all names in `AlgebraicGeometry.ProEtale`):

- `spStratifiedScalarCone_naturality`.
- `spStratifiedFiniteMap_naturality`.
- `spStratifiedRingMap_isIso`.
- `spStratifiedScalar_finite`.

Added zero holes. The private helper `spStratifiedScalarFinite` is fully proved.
The three original holes left, unchanged, are:

- `spStratifiedOrdinaryComparison_existsUnique`.
- `sp_stratified_reduction_postnikov_comparison`.
- `sp_stratified_reduction_homology_comparison`.

All three remain attached to `lem-sp-stratified-reduction-postnikov-comparison`.
Their existing docstrings and six-step source proof plan are retained. The main
Postnikov and derived-comparison assertions are not claimed proved.

## No longer needed

Removed these nine proof imports, unused by the completed proofs or the public
statements and definitions (confirmed by compiling the entire module):

- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `WeilConjectures.CategoryTheory.TruncationTriangle`.
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Sheaf.Paper.ProEtaleFiniteModelStalks`.

No mathematical dependency nodes are withdrawn: the unproved comparison and
Postnikov steps may still need their listed dependencies. These import removals
claim only that the present Lean module no longer needs those direct imports;
they do not assert that the modules leave the global targets closure. Every
existing public import remains unchanged. No source-library declaration or module
is removed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or repair. The DAG's coefficient identifications can be
implemented directly from the already proved finite constant tower preservation
and naturality APIs. No separate argument using continuous integral functions is
needed for the completed-ring isomorphism. This proof uses only finiteness of the
specific coefficient tower, not preservation of arbitrary inverse limits.

The edge cases require no new assumption: the minimum level is exponent one;
cofinality handles ramified coefficient fields; quotient surjectivity and limit
universal properties do not require a nonempty scheme. The proof does not need
the immersion assumption beyond retaining the original theorem signature.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
