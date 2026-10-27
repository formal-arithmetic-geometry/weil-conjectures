## What changed

Filled `WeilConjectures.IntegralSystemRealization.basicSystemShiftResolutionCalculus`
by assembling its thirteen fields. The exact-operation model squares follow from
Mathlib's identity cochain components and the shift compatibility of
`mapDerivedCategoryFactors.hom`. The actual direct-image unit is identified with
the mate of the exact factorization using the recorded transpose equation and
the ordinary adjunction triangle identity. Its shift equation gives the square
on every supplied simultaneous K-injective resolution. The mate property is
Mathlib's `Adjunction.commShift_of_leftAdjoint` for the specified shift.
The four individual tensor model fields are projections from `tensorShifts`.

Three new modules isolate the remaining tensor arguments: simultaneous
representative normalization, prescribed system tensor coherence, and the
zero/addition laws of the prescribed completed-tensor slots. These are proper
parts of original proof Steps 4--6, on a single arbitrary scheme and independent
of the operation package and geometric arrows. The parent proof has no holes.
Its public imports, definitions and theorem signature are unchanged.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.basicSystemShiftResolutionCalculus`.
Added three holes, all public named theorems in separate modules:

- `WeilConjectures.IntegralSystemRealization.systemTensorShiftRepresentativeModels`
  (`lem-pur-system-tensor-shift-representative-models`).
- `WeilConjectures.IntegralSystemRealization.systemTensorShiftCoherence`
  (`lem-pur-system-tensor-prescribed-shift-coherence`).
- `WeilConjectures.IntegralSystemRealization.completedTensorSlotShiftLaws`
  (`lem-pur-completed-tensor-prescribed-slot-shift-laws`).

This is a decomposition, not a sorry-free proof of the overall mathematical
result: one original hole closed, three strictly smaller holes added. The parent
has zero remaining holes, and each added theorem carries a source and a complete
proof in words. No definition or private theorem contains a hole.

## No longer needed

Removed these private proof imports from the parent:

- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`
- `Sheaf.SixFunctors.DiagramPullbackMonoidalShiftModels`
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`
- `Sheaf.Algebra.Homology.TotalTensorSignedCoherence`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`

The parent no longer needs `lem-coef-semilinear-derived-sections`,
`prop-pur-kinjective-resolutions-exist`,
`lem-sf-kinjective-derived-map-computation`, or
`lem-sp-canonical-right-derived-adjunction-shift` in its proof. It starts with an
already supplied K-injective resolution and the package's actual normalized
adjunction, so neither resolution existence nor a separate computation theorem
for a differently presented derived functor is needed. The system tensor model
and coherence lemmas, K-flat shift stability, signed total-tensor coherence,
well-definedness and fully faithful localization remain needed below the three
new tensor nodes, whose imports record that work. The independent completed
right-shift existence theorem is unnecessary to prove the normalized field,
which is already part of `TensorShifts`; its existing public import is retained.
No module is withdrawn, and no global closure pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned resolution-existence and arbitrary-resolution comparison machinery
is unnecessary for the exact propositions actually recorded by the parent.
The package's transpose equation identifies its derived unit directly, avoiding
any inference from evaluated K-injectives or evaluation of derived arrows.
The original Step 4 still needs identification between the generic diagram
model constraints and the actual closed tensor/comparisons in `calculus`; the
new coherence node records that identification explicitly. The new statements
retain arbitrary K-flat pairs, including ones without flat terms, using a
further flat-term K-flat resolution in the proof in words.

Edge cases checked in the mathematical statements: zero complexes, zero and
negative shifts, one or both shifts odd (the symmetry sign is retained), and
empty schemes. No extra invertibility, properness or flatness hypothesis was
introduced. The unit `sk-thm-sf-compatibility` and its route are unchanged.

## New nodes

`lem-pur-system-tensor-shift-representative-models` is original Step 4's
simultaneous generator formula and comparison square, assembled from the two
already normalized slots. It retains every K-flat pair and strict transition.

`lem-pur-system-tensor-prescribed-shift-coherence` is the rest of original
Step 4: slot laws and the actual associator and normalized Koszul-symmetry
squares. It uses the existing generic diagram theorem and resolving descent;
it is independent of all geometric-operation fields of the parent.

`lem-pur-completed-tensor-prescribed-slot-shift-laws` is original Steps 5--6's
zero/addition descent for the already prescribed completed tensor comparisons.
The finite signed formulas, product and cone normalization, and localization
argument are recorded in its proof. No new data is chosen from mere existence.

Validation: the three new statement modules compiled through `lcompile.py`; the
parent proof is checked through the same compiler. Node Lean signatures
were checked verbatim against their source. All direct DAG citations exist and
the `proof_deps` lists equal the unions of the proof steps. Existing definitions,
the parent theorem signature and all public imports were checked verbatim.
The associator exponent identity and parity of the symmetry exponent identity
were checked on all integer inputs from -3 through 3, in addition to the
symbolic proof in words.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
