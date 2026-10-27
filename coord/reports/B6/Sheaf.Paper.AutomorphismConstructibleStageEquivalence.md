## What changed

Reduced `WeilConjectures.automorphismConstructibleStage_comparison_system` from its
existence-and-agreement statement to the already stated simultaneous realization
theorem and one whole-system counit square. Added private proof imports of
`Sheaf.Paper.SimultaneousIntegralPullbackComparisons` and
`Sheaf.Paper.IntegralScalarPullbackCompletionNormalization` to the item.

The new module `Sheaf.Paper.IntegralScalarPullbackCompletionNormalization` proves
`WeilConjectures.integralScalarPullbackCompletion_normalization`. Two proved private
category-theory helpers use counit naturality and injectivity of the adjunction Hom
bijection to lift the system square to the prescribed lambda/mu equality. The item
then cancels mu and obtains agreement with the actual tensor/completion comparison.
The representative calculation is isolated in
`Sheaf.Paper.IntegralScalarPullbackCounitCompatibility`. Every existing statement,
definition, visibility and public import is preserved. No consumer adaptations or
change record are needed. The unit route is unchanged.

Validation: both new modules passed `lcompile.py --all` without warnings or
errors (48.0 and 47.0 seconds in result `3670d2500060f919c3044b99`). The final
parent passed its single-file check without warnings or errors in 49.6 seconds
(result `649e709837492717364add06`). The final parent uses Mathlib's
`Iso.eq_comp_inv` directly, avoiding explicit rewriting and reduction of the
comparison constructor. It also uses synchronous elaboration (`Elab.async false`)
and locally keeps `integralDerivedPullback`, `scalarPullbackCompleted`,
`integralComparisonLambda`, and `integralComparisonMu` irreducible with transparency
respected during this proof. These settings prevent reduction into the large
operation constructions and leave the interfaces unchanged. All profiling options
have been removed.

## Proved and sorry left

Closed the comparison-system hole (one of five at the start of the session,
and one of six in the current shared source):
`WeilConjectures.automorphismConstructibleStage_comparison_system`.
This is a decomposition, not a net hole reduction: one lower hole is added.
Also proved the new
`WeilConjectures.integralScalarPullbackCompletion_normalization` by an explicit
adjunction calculation.

Five original holes remain, all on
`lem-sf-automorphism-constructible-stage-equivalence`:

- `WeilConjectures.automorphismStageQbarSquare_existsUnique`.
- `WeilConjectures.automorphismConstructibleStage_integral_coherence`.
- `WeilConjectures.automorphismConstructibleStage_integral_shifts`.
- `WeilConjectures.automorphismConstructibleStage_descended_shifts`.
- `WeilConjectures.automorphismConstructibleStage_inverse_comparisons`.

One new hole remains:
`WeilConjectures.integralScalarPullbackCounit_compatibility`, on
`lem-sf-integral-scalar-pullback-counit-compatibility`. Its docstring contains the
strict quotient-system proof with the source, the actual completion maps, both Roos
coordinates, and the independence-of-representative argument. It is the geometric
scalar square in the derived category of entire coefficient systems. It asserts
neither global existence nor composition, tower or shift coherence. Those parts of
the parent come from the existing simultaneous realization theorem.

There are six holes in the delivered files: five original and one new. No holes
occur in definitions, private helpers or partially completed proof bodies.

## No longer needed

None. No existing imports, nodes or modules are withdrawn. The other five holes
still use their recorded routes. The existing simultaneous theorem handles the
coherent-system existence step, so no duplicate existence or coherence lemma is
introduced. The new calculation imports only its statement interfaces and its
whole-system compatibility lemma; it does not import an isomorphism-only scalar
comparison theorem, which would not apply to arbitrary f.

## Where the brief, the DAG or earlier work was wrong

The source had five holes when the session started. During the session the
shared source restored the integral-coherence hole and removed its former helper
proofs, returning the baseline to six. The final packet preserves that update;
it does not restore the removed E1 proof. The simultaneous realization theorem
provides coherence but does not also identify its comparison with
`integralPullbackScalarComparison`; a direct application alone is insufficient.
The existing isomorphism-scalar-agreement theorem requires `IsIso f`, while this
clause quantifies over every morphism. The scalar tower theorem has the relevant
whole-system equation but requires additional completed-operation models and
tensor models absent from the supplied `IntegralComparisonSystem` interface.
The new remaining lemma isolates exactly that representative-normalization gap.

Edge checks: the zero object and empty scheme yield zero arrows; identity scheme
and coefficient maps reduce to their prescribed unit maps. The general argument
uses derived change of rings and does not assume flatness of ramified finite
quotient coefficient maps. The lifting proof uses the actual adjunction Hom
bijection, not detection by finite evaluations.

## New nodes

`lem-sf-integral-scalar-pullback-counit-compatibility` records the remaining entire
system square, its source and complete proof plan, and its one-statement module.
It is the strict-system part of the parent's scalar-agreement argument.

`lem-sf-integral-scalar-pullback-completion-normalization` records the proved lift
of that square by counit naturality and adjunction injectivity. Its one-statement
module is used directly by the parent. The parent's proof and proof dependencies
are updated to record this assembly. No change records are added because no
existing statement or definition changed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
