## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.negativeKoszulTensorRealization`
by induction on the ordered list of generators. The induction is proved for an
arbitrary additive coefficient functor to the module sheaves; this avoids
unfolding the concrete scalar-extension functor during the tensor calculations.
The successor comparison is the binary tensor comparison followed by the tensor of the first-factor comparison
and the tail comparison. The proof separately verifies the transition square
and the empty-subset unit equation using the total-tensor inclusions.

The empty case is derived rather than assumed: the normalized rank-one
comparison at scalar zero proves that the prescribed coefficient-unit map is an
isomorphism. The standard Mathlib comparison with a single complex then gives
the empty tensor and its unit equation.

Added two proof imports and two independent intermediate statements:
`Sheaf.Paper.WeilNegativeKoszulFactorRealization` (one exterior factor, without
any tensor induction) and `Sheaf.Paper.WeilCompletedRealizationTensor` (binary
total tensors of arbitrary complexes, without any Koszul complexes). These are
steps 1 and 2 of the original plan; their combination and the entire induction
are proved in the assigned module. Existing statement signatures are unchanged. The old theorem-scoped overrides
that disabled transparency checks are removed; the proof uses explicit component
equations and one layer of the basis recursion instead.

Validation: the assigned module compiles without errors or warnings through
`lcompile.py` in 51.7 seconds. Both intermediate modules also compile individually
in the packet compilation (18.5 and 13.1 seconds). The original theorem signature
is preserved, the new node statements match their Lean signatures, and every Lean
line is at most 100 characters.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.negativeKoszulTensorRealization`
(`lem-weil-pbc-negative-koszul-tensor-realization`).

Added two holes, each the entire proof of a named public theorem in its own module:

- `AlgebraicGeometry.Scheme.negativeKoszulFactorRealization`
  (`lem-weil-pbc-negative-koszul-factor-realization`).
- `AlgebraicGeometry.Scheme.completedRealizationTensor`
  (`lem-weil-pbc-completed-realization-tensor`).

This is a decomposition, not a sorry-free proof: one original hole closed, two
strictly different lower obligations added. No sorry remains in the assigned
module. No definition or instance contains a new hole. The regular coefficient
unit and the empty-tensor comparison are proved without a third obligation.

## No longer needed

No module is globally pruned and no original import is removed. The original
exterior-basis dependency is now needed only by the one-factor intermediate;
the assigned module uses its conclusion through that comparison. All original
mathematical dependencies remain needed either directly or by an intermediate.
The positive Koszul complex, internal Hom and duality comparisons are not used.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies define the relevant constructions and the exterior
basis but do not state their normalized coefficient-realization or binary
tensor comparisons. These are distinct omitted bridges in steps 1 and 2 of the
original plan, rather than a reason to restate the arbitrary-rank obligation.
The arbitrary-rank tensor induction is now implemented, including transitions,
units, rank zero and its prescribed normalization.

Searches used LeanSearch for one-generator Koszul/two-term comparisons,
LeanFinder for preservation of total tensors, Loogle for the single-complex
comparison, and source grep for Koszul realization and tensor comparison APIs.
Mathlib supplies `singleMapHomologicalComplex`, its degree-zero component
formula, and total-tensor functoriality. The adopted source library also supplies
`mapBifunctorComparison`, but requires a normalized module-level comparison for
the present coefficient functor, which its declarations do not provide.

The source checks include Stacks algebraization Tag 0A0E and Modules on Sites
Tags 03D8, 03EK and 0GMW, and the current blueprint unit. The argument excludes
no zero ring, empty site, zero/unit scalar, or empty generator list. No unit
statement or step is bypassed.

## New nodes

`lem-weil-pbc-negative-koszul-factor-realization` states only the rank-one
exterior-to-two-term scalar realization, with its transition and unit. Its proof
uses the zeroth and first exterior equivalences and vanishing higher powers,
then realizes the resulting two bases. It does not compare tensors of factors.

`lem-weil-pbc-completed-realization-tensor` states the natural binary tensor
comparison for completed constant realization and its normalization on arbitrary
maps into the (0,0) summand. It does not mention any Koszul complex, exterior
power, generator list, or inverse-system transition. Its proof is the balanced
tensor/sheafification comparison applied to each total summand, with the actual
coefficient units. No definition or existing public interface is changed, so
no change record is needed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
