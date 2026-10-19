## What changed

Proved the normalized rational shift is additive, the scalar-associator shift equation,
zero- and addition-shift naturality on the quotient, additivity of the descended shift,
the included zero-object assertion, finite-graph representation, simultaneous equality
detection, the descended shift coherence and inclusion comparison laws, and
commonStageCalculus. A proved private helper assembles the generic
specification before specializing to the concrete coefficient system, avoiding expensive
unfolding of its definitions. Statements and existing definitions are unchanged. The file-local linter setting is
recorded in `coord/changes/common-stage-calculus-linter.md`.
Added the proof-only Mathlib.Data.Fintype.Order import for Finite.exists_le.
The unused-section-variable linter is disabled to retain the existing signatures of
lemmas whose completed proofs no longer use all their section assumptions.

## Proved and sorry left

Closed 11 of 19 original holes; added zero holes and split off zero.

Closed declarations:

- `pbcRationalShiftAdditive`
- `pbcStageShift_coherence`
- `pbcPairShiftZero_naturality`
- `pbcPairShiftAdd_naturality`
- `pbcPairShift_laws`
- `pbcStageInclusionShift_laws`
- `pbcPairShift_additive`
- `pbcPairZero_isZero`
- `pbcFiniteGraph_representation`
- `pbcFiniteEqualities_detection`
- `commonStageCalculus`

Remaining original declarations (all attached to
`prop-weil-pbc-common-stage-calculus`):

- `pbcIntegralStableShift`
- `pbcIntegralShiftLinear`
- `pbcRationalShift_exists`
- `pbcRationalizationShift_exists`
- `pbcScalarShift_exists`
- `pbcScalarAssociatorCommShift`
- `pbcStageFiniteBiproducts`
- `pbcPairFiniteBiproducts`

The main theorem is assembled from the existing named local obligations and upstream
proved StageSystem facts; its axiom closure still includes the remaining obligations.
No new unproved intermediate statement was added.

Validation: the resumed lcompile.py check compiled the final module in 10.5 seconds
with no errors or warnings on 2026-10-19. The required delivery dry run is rerun
against the current sources before pushing.

## No longer needed

No dependency module or DAG node is pruned. The remaining original holes retain the
planned finite-stage construction and coherence dependencies. No import was removed.
The equivalence, transport cocycle, identities, common-stage composition and inverse
shift isomorphisms use the existing upstream and Mathlib APIs directly.

## Where the brief, the DAG or earlier work was wrong

The module was temporarily absent during the shared checkout refresh and then became
available unchanged. Two compilation attempts received no server answer; retries worked.
A concrete assembly proof exceeded the compiler limit through elaboration; moving the
same argument to a proved generic private helper restored normal compilation time.
No mathematical statement or definition repair was necessary.

The retained sandbox was checked against the current source. The subsequently added
proof-dependency import `Sheaf.Paper.PbcScalarExtension` was restored. The two further
shift coherence obligations use Mathlib shift laws mapped through the stage inclusion;
identity inclusion comparisons cancel the included shift isomorphisms. The existing
proof route and DAG dependencies are unchanged.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
