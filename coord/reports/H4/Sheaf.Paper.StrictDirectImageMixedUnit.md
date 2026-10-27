## What changed

Proved the assembly of `strictDirectImageMixedUnit` from three strictly smaller obligations.
`StrictDirectImageMixedUnitData` holds the existing definitions with identical signatures and
bodies; the original module publicly re-exports them. This avoids an import cycle for the new
construction and comparison modules. The change record is
`coord/changes/strict-mixed-unit-shared-data.md`.

The private helper `scalar_square_unit` transposes the scalar-linear comparison, applies unit
naturality, uses naturality of restriction/direct image, and cancels the scalar-reduction
isomorphism. The private helper `mixedUnit_bijective` identifies the system lift map with a
composite of two Hom equivalences. The main theorem constructs CoherentLaws using these actual
proofs, then obtains FiniteLaws by finite evaluation and pairs the conclusions.

## Proved and sorry left

Original holes: 1. Closed by decomposition:
`WeilConjectures.StrictDirectImageMixedUnit.strictDirectImageMixedUnit`.

Three holes added, each public in its own module with a source and proof in words:

- `WeilConjectures.StrictDirectImageMixedUnit.strictMixedSystemModels`
  (`lem-weil-strict-mixed-system-models`): Steps 1--3, normalized auxiliary system models.
- `WeilConjectures.StrictDirectImageMixedUnit.strictMixedScalarSquare`
  (`lem-weil-strict-mixed-scalar-square`): the scalar-linear square of Steps 4--5, before
  restriction and precomposition with the unit.
- `WeilConjectures.StrictDirectImageMixedUnit.strictMixedFiniteEvaluation`
  (`lem-weil-strict-mixed-finite-evaluation`): evaluate coherent laws, and transport the
  finite scalar-adjunction Hom bijection.

This is a decomposition of one upper hole into three lower holes, not a net proof closure.
The item module and relocated data module contain zero sorry.

## No longer needed

No mathematical dependency or module is withdrawn. Removed direct private imports:
`SemilinearDerivedSections`, `SheafRingDerivedCoefficientAdjunction`,
`RingedToposDerivedPushforwardComposition`, `CompletedCoefficientPushforwardComparison`,
`RingedTowerPushforwardLimitComparison`, `SequencePushforwardLimitProjections`,
`SuccessiveDerivedQuotientNormalization`, `FiniteFreeCompletedScalarComparison`,
`CompletionUnitStrictQuotientModel`, and `RingedComparisonTensorAdjunction`.
The corresponding mathematical constructions remain in the new nodes' proof plans;
the split statements themselves only import the shared interfaces.
All existing public imports are retained through the public data-module re-export.
The original six-step plan remains below the three obligations. The item directly uses the
new nodes; its old generic tools remain transitively needed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's scalar-unit cancellation is formal once the scalar-linear
square has been constructed; this part and the whole-system unique lift are now actual Lean.
The generic dependency declarations do not directly instantiate the required normalized
models on these particular sites. Those instantiations and the remaining mate/evaluation
transports have been isolated as genuine argument steps, rather than repeated as the entire
original statement.

Edge checks for the new statements: identity coefficients, the zero input, exponent n=0,
and ramified coefficient inclusions. The scalar square is stated before using evaluation or
assuming flatness; the finite-evaluation implication assumes the full coherent normalization.
The general model theorem retains properness, finite type, separatedness and invertibility
of l, so it does not require constructibility for an arbitrary nonproper image.

## New nodes

`def-weil-strict-mixed-unit-data` records the unchanged relocated interfaces.
`lem-weil-strict-mixed-system-models` supplies actual normalized data and evaluations, but no
mixed-unit square. `lem-weil-strict-mixed-scalar-square` supplies the scalar-linear square,
without constructing models, finite evaluations, or lift bijections.
`lem-weil-strict-mixed-finite-evaluation` evaluates an already constructed coherent law.
All have logged LeanSearch, Loogle/LeanFinder and Mathlib grep searches. The categorical search
results give the Hom-equivalence identities used in the proved assembly; none states the
specialized normalized constructions.

The existing generic tool uses are carried in each new node's split report with their
original reasons. These are requests to retain the already reviewed tools in the smaller
steps, not changes to the unit route or new maintainer approvals.

Validation: the independent categorical unit calculation compiled successfully in 1.6 s.
The unused simp argument reported in that probe was removed from the delivered proof.

The shared data and three split modules compiled cleanly (48.3 s, 47.4 s, 48.1 s,
and 51.5 s respectively). The scalar-square assembly checked in the item compile;
its remaining helper transport was normalized explicitly using `Iso.app_inv`.

The item theorem compiled successfully in 25.1 s with all proof goals closed.
The only warning was an empty line within the helper command; it was removed before
delivery. The delivery preflight performs the final compilation.

Delivery preflight correction: the data node now records the complete verbatim
`CoherentLaws` signature, including all binders and its result type; its former
short declaration header was rejected by the signature gate. All module compilation
and axiom probes passed on the first delivery attempt.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
