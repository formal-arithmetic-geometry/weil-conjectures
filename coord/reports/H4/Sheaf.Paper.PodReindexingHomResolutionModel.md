## What changed

Proved `WeilConjectures.podReindexingCoefficient_existsUnique` in
`Sheaf.Paper.PodReindexingHomResolutionModel`, following Steps 1--3 of
`lem-pod-reindexing-hom-resolution-model`. A proved private helper assembles the
constant coefficient comparisons into a natural isomorphism and identifies its
components with the recorded constant-section-normalized ring maps. The finite
quotient transitions are therefore natural. Reindexing preserves the inverse
limit of this tower; forgetting commutativity is fully faithful, so its limit
comparison lifts to the recorded commutative ring sheaves. The projections prove
the completed normalization, and their joint uniqueness proves uniqueness of the
whole finite/completed family. All existing imports are retained; no new import
is required, since the site-equivalence interfaces are already available.

All public statements and definitions remain unchanged. In particular the
coefficient family continues to be selected from its uniqueness characterization.
The proof covers arbitrary scheme isomorphisms without invertibility or size
hypotheses beyond those of the original coefficient theorem.

## Proved and sorry left

Closed one of the four original holes:
`WeilConjectures.podReindexingCoefficient_existsUnique`.
Added no holes and split off no statements.

Three existing holes remain unchanged, all attached to
`lem-pod-reindexing-hom-resolution-model`:

- `WeilConjectures.podReindexing_resolution_preservation`.
- `WeilConjectures.podReindexing_hom_resolution_model`.
- `WeilConjectures.podReindexing_roundTrip_shift`.

The private helper `podReindexingConstantComparison` is proved. Its proof uses the
existing site equivalence and Mathlib's compatibility of sheafification with
continuous, cocontinuous reindexing. These are the same declared dependencies as
in the original proof plan.

## No longer needed

None. No imports, nodes, modules, or unit steps were removed. The unfinished
resolution, Hom, and round-trip theorems retain their existing dependencies. The
coefficient proof uses the recorded constant comparison, completed coefficient
tower, and inverse-limit universal property as planned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction or definition repair was needed. The listed
rework entry is historical: the assigned module is present in the current shared
source and was copied from that source. No quarantined module was withdrawn.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
