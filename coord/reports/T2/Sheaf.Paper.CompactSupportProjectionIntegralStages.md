## What changed

Replaced the hole in `WeilConjectures.compactSupportProjectionFormula_integralStages`
with an assembly of the six projection laws. The target signature and all definitions
are unchanged. Proof imports are private.

The private helper `integral_reductions_conservative` proves conservativity of all
positive reductions on the actual integral constructible category. It uses evaluation
conservativity for derived coefficient systems, the reduction/total-limit adjunction,
and its invertible units on complete objects. A universe-zero auxiliary finite-field
datum translates canonical completeness into the existing Roos completeness predicate.
This argument detects isomorphisms, not equality of arrows by finite reduction.

The private helper `projection_naturality` evaluates naturality of the specified
projection natural transformation in both variables. Compactification independence
uses `FixProjectionCompactification.comparison`. The remaining laws use the two new
bridges described below. The same construction applies to every finite coefficient
field by forming a datum from its first finite level and its recorded integral and
closure operations.

Validation: all three Lean modules compile cleanly through `lcompile.py`. The main
module took 14.6 seconds; the two new statement modules took 54.1 and 53.3 seconds
in their successful set compile. The original public theorem signature is byte-identical;
only the parent node's `proof`, `proof_deps` and `proof_origin` fields changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.compactSupportProjectionFormula_integralStages`
(node `lem-sf-projection-integral-stage-laws`). The item's module has zero holes.

Added two holes, one public theorem per new module:

- `WeilConjectures.integralStageProjection_reduction`, in
  `Sheaf.Paper.IntegralStageProjectionReduction`
  (node `lem-sf-integral-stage-projection-reduction`).
- `WeilConjectures.integralStageProjection_structuralIdentities`, in
  `Sheaf.Paper.IntegralStageProjectionStructuralIdentities`
  (node `lem-sf-integral-stage-projection-structural-identities`).

This is a decomposition: one upper hole closed and two strictly narrower holes added,
not a net reduction in holes. The arrow comparison asserts no invertibility. The
structural-identity theorem asserts composition, pentagon and proper coincidence,
excluding invertibility, naturality and compactification independence. The Lean proof
combines these parts with finite-stage invertibility, proved conservativity, naturality
and the existing compactification theorem. It does not assume the original conclusion
under another name. Existing imported theorems may themselves depend on `sorry`.

## No longer needed

No original imports were removed and no module is withdrawn or globally pruned.
The original item had only its public statement import.

The direct use of `sk-lem-pe-derived-nakayama` is replaced by conservativity through
normalized reconstruction and the reduction/total-limit adjunction. The original
concrete reduction-square and integral-cone dependencies now belong to the narrower
reduction bridge. Integral coherence realization now belongs to the structural
identity bridge. These latter nodes and modules remain needed; they are not claimed
as pruned. The parent DAG proof and proof-dependency list follow the assembly actually
written in Lean.

## Where the brief, the DAG or earlier work was wrong

The original dependencies express the concrete projection and its system realization,
but do not directly state their comparison with the exchange transformations recorded
in an arbitrary `SixFunctorOperationDatum`. The new reduction bridge supplies exactly
that normalization comparison. Likewise the generic system-realization theorem needs
to be instantiated on the datum's composition and proper-coincidence routes; the
structural bridge isolates those equations. No false statement or definition repair
is claimed. There are no forced adaptations or source-library edits.

## New nodes

`lem-sf-integral-stage-projection-reduction` compares the actual reduced integral
projection arrow to the normalized finite projection arrow. Its endpoint isomorphisms
and commutative square come from the concrete reduction/cone declarations and the
operation normalization. It includes every positive exponent and retains the arbitrary
bounded constructible first input. Zero inputs, the empty scheme, identity
compactifications and exponent one use the same canonical comparisons.

`lem-sf-integral-stage-projection-structural-identities` states only composition,
pentagon and proper coincidence. Its proof plan specializes the existing coherent
system realization and integral coherence equations before applying total limit.
It does not infer equality of integral maps from their finite reductions and does
not invert projection. The pentagon has the same transported compactification and
unrestricted bounded constructible input as the original law.

Both nodes record source locations, their actual Lean signatures, proof dependencies
and the three completed Mathlib searches. No change record is required because no
existing signature or definition changes.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
