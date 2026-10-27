## What changed

Added and proved CategoryTheory.brownHypothesesFor_padicIntegers_iff_ext_bounded in the
assigned module. Over a separated finite-type scheme over an arbitrary field of positive
characteristic different from ell, the integral Brown bundle is equivalent to bounds on
Ext(C,N) for each constructible C, uniform over constructible N. No bound is asserted
without a hypothesis. Necessity applies the existing Brown uniform-heart bound after
Dctf=Dbc; sufficiency applies integralConstructibleCompactness with explicit bounds and
transports its dependent coproduct/compactness assertion across Loc(Dctf)=Loc(Dbc).

Added the proved private helper compactness_of_brown_coefficientIso. It uses the existing
canonical Hom-map comparisons and preservation of constructible finite-Tor objects under
coefficient isomorphisms. The private six-case finite-field assembly now uses the new
criterion and integralConstructibleExt for coefficients isomorphic to O_E. Other cases
retain the original skeletal compactness proof. Every original signature, visibility,
public import and non-theorem body is unchanged; no other Lean module is adapted.

New proof imports name IntegralConstructibleCompactness, IntegralConstructibleExt,
LocalizingClosureCtfEqualsBc, CondensedCoefficientIsoConstructible, CharAndCard and
BrownHypothesesGeneration. The last is imported with all for its proved private canonical
comparison helpers. BrownHypothesesSmall is imported with all to use its proved
constant_heart_zero helper. Neither use appears in any public signature.

Updated the main and finite-field nodes to match this proof, and added the integral
criterion node. Change record: coord/changes/E3-brown-integral-ext-criterion.md.

## Proved and sorry left

Original holes closed: 0 of 1. New holes: 0. Split-off holes: 0.
The sole sorry remains CategoryTheory.brownHypotheses, node sk-lem-brown-hypotheses,
with its original statement and STATEMENT-DISPUTED diagnostic. This delivery proves the
integral criterion and its use in the supported finite-field assembly; it does not claim
to prove or decompose the unsupported unconditional arbitrary-field assertion.

The new criterion and private transport helper have complete Lean proofs and do not use
the disputed theorem. The source-parser comparison confirms all original declaration
signatures and non-theorem bodies are preserved. The complete revised module compiled through the required remote compiler in 55.6
seconds, exit 0; its only diagnostics were the two development-profiler style warnings.
Both profiling options are removed from the delivered source. deliver3.py performs the
final compilation, declaration-axiom probe and packet checks before pushing. The first
delivery probe compiled in 57.0 seconds but reported an isolated-bullet formatting warning;
the bullet was merged with its next tactic before rerunning delivery.

## No longer needed

For coefficients isomorphic to O_E, the finite-field assembly no longer needs to choose
a small skeleton or invoke the finite-field representative compactness theorem: explicit
Ext bounds and the integral criterion give its compactness clause directly. These steps
and the representative compactness module remain needed for the other coefficient cases.
No import, node or module is withdrawn, and none is claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the remaining theorem asserts compactness over an arbitrary field
without the needed cohomological finiteness hypothesis. The finite/rational compactness
inputs require the geometric field of a finite-field datum, and the integral compactness
input takes explicit Ext bounds. Finite type over an arbitrary field does not supply
those bounds. Both current callers, LocalizingExceptionalAdjoint and
ExceptionalInverseImageExistence, still assert arbitrary-field results, so replacing the
original theorem with its finite-field specialization would break their proof route.
Its original natural-language Kummer/infinite-transcendence diagnostic remains intact;
this delivery does not claim a formal field-cohomology counterexample.

The new theorem makes the integral hypothesis exact: uniform bounds on constructible
Ext are both sufficient and necessary, rather than merely a conditional obstruction.
This uses the actual parameters of integralConstructibleCompactness, not a new
unconditional compactness assumption or a renamed hole. Edge cases checked from the
statement include an empty scheme, a zero constructible source, negative chosen integer
bounds (enlarged by toNat), and fields lacking such bounds. In the latter case the
criterion asserts an equivalence, not a false Brown bundle. All coproduct indexing
universes and ambient unbounded derived Hom groups match the existing statements.

The source-parser check and downstream census found no consumer changes to make.
No object is chosen from an unproved mere-existence theorem, no axiom is added, and
the unit's integral compactness route is retained.

## New nodes

lem-sfb-brown-integral-ext-criterion records the new proved equivalence. Its source is
paragraph 2 of the current Brown-hypotheses proof, the explicit-bound integral compactness
theorem (clause 3 of sk-prop-int-compactness-compact), and the existing finite-support
necessity. Its dependencies are the integral Tor/closure equality, the Noetherian
Brown compactness criterion, the uniform-heart Ext bound, coefficient smallness and
integral compactness. LeanSearch, LeanFinder, Loogle and direct source/Mathlib searches
found no existing exact equivalence. Whole-blueprint searches found no duplicate.
The only new node is proved, and no new module or hole is introduced.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
