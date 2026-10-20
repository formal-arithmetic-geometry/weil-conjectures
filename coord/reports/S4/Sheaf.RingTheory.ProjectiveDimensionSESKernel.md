## What changed

Restored the quarantined module `Sheaf.RingTheory.ProjectiveDimensionSESKernel` with
its existing theorem proved against the adopted upstream projective-dimension API.
The public import of the retired duplicate `Sheaf.RingTheory.GlobalDimension` was
replaced by `WeilConjectures.RingTheory.GlobalDimension`, which provides the adopted
`ModuleCat.HasProjectiveResolutionLE` predicate. A private import of
`WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension` supplies the proved
bounded-resolution/projective-dimension equivalence. The proof converts both
resolution hypotheses to `HasProjectiveDimensionLE`, applies Mathlib's
`ShortExact.hasProjectiveDimensionLT_X₁`, and converts the result back. The node's
proof route and dependency were updated accordingly.

## Proved and sorry left

Closed zero local holes: `Ring.projectiveDimensionLE_of_shortExact` was already a
complete proof in the quarantined source, and remains complete. Added zero holes and
split off zero statements. No `sorry` remains in the delivered module. Its proof
uses the existing upstream theorem
`ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE` and therefore does
not introduce any new axiom or definition. A separate single-file compilation with
`#print axioms Ring.projectiveDimensionLE_of_shortExact` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` (1.2 seconds). The delivered theorem
also compiled cleanly in 1.0 second. The bound-zero case gives a projective kernel
when the middle term is projective and the quotient has projective dimension at
most one; the degree shift is `m + 1`/`m + 2` in all cases, including zero modules.

## No longer needed

The retired `Sheaf.RingTheory.GlobalDimension` import is no longer needed.
The Mathlib projective-dimension proof import is retained, as its short-exact lemma
is used directly. The old dependency on
`lem-weil-pbc-projective-dimension-ext-characterization` is replaced by the existing
`lem-weil-pbc-projective-resolution-ext-degree` node, whose Lean declaration is the
adopted upstream bounded-resolution bridge. The old
`WeilConjectures.RingTheory.ProjectiveResolutionExtCharacterization`
proof import is removed. No mathematical nodes are withdrawn, and no entire module
is claimed pruned from the targets’ closure.

## Where the brief, the DAG or earlier work was wrong

The rework failure was caused by importing the local duplicate global-dimension
module after the upstream source library had adopted the same declarations, producing
the duplicate declaration error for `Ring.HasFiniteGlobalDimension`. The theorem's
mathematical statement and signature remain unchanged; only its dependency imports
and proof route needed migration to the upstream declarations.

Change record: `coord/changes/projective-dimension-ses-kernel-upstream-import-S4.md`.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
