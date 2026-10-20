## What changed

Restored Sheaf.Paper.LevelwiseAdicTruncations from the exact quarantine source named by
coord/rework.tsv. Repaired the recorded unknown-identifier error in
pbc_levelwise_truncations_constructible by changing its local-model stratification binder
from the retired LocallyClosedStratification to the current Scheme.Stratification.
Under the existing IsNoetherian hypothesis, locally closed strata are constructible,
so this is the same finite stratification required by the source.

Gave the existing generic standard-localization instances
reductionRingModulesHasDerivedCategory and pbcTowers_hasDerivedCategory local priority
2000. Their values remain HasDerivedCategory.standard; this avoids expensive searches
through specialized coefficient constructions. Kept completedAdicDerivedChange and
pbcDerivedScalarAdjunction locally irreducible so
elaboration uses their published functor/adjunction interfaces. Added the proved private
scalar_unit_transport lemma (the adjunction unit's naturality, followed by functoriality
and associativity). Used it in the lower and upper endpoint proofs of
pbc_levelwise_truncation_transitions, replacing two broad simpa calls with simpa only
on explicit transport equations. All other definitions and theorem proofs are preserved.
No global instance, external definition, public import, or mathematical dependency changes.

Change record: coord/changes/F1-levelwise-adic-stratification-rework.md. It records the
old/new signature and all seven quarantined direct consumers. No live consumers exist.
No consumer adaptation is forced; archived consumers retain their separate rework tasks.
The node attachment and proof route are preserved: the transport helper implements the
unit-naturality step already described in the node, with no new dependency or split.

Verification: the final complete module compiled cleanly through lcompile.py in
32.7 seconds, with no profiler enabled. Full-module scratch profiling and axiom probes
were used during the timing investigation; the delivery tool additionally runs its
unmodified axiom probe and preflight. Searches used msearch.py leanfinder, loogle, grep
and rg on the current stratification and bounded-constructibility APIs. The source
Noetherian constructor, node and unit record were read; the unit has no realized steps.

## Proved and sorry left

This is the listed quarantine repair, not a proof decomposition. Holes closed: 0 of 7.
Holes added or split off: 0. The seven original named theorem holes are retained verbatim,
all attached to prop-weil-pbc-levelwise-truncations:

- AlgebraicGeometry.Scheme.pbc_adic_levelwise_truncations
- AlgebraicGeometry.Scheme.pbc_reduction_adic_tower_laws
- AlgebraicGeometry.Scheme.pbc_levelwise_tor_of_uniformizer_injective
- AlgebraicGeometry.Scheme.pbc_levelwise_truncations_constructible
- AlgebraicGeometry.Scheme.pbc_levelwise_truncation_counterexample
- AlgebraicGeometry.Scheme.pbc_levelwise_truncation_origins
- AlgebraicGeometry.Scheme.pbc_levelwise_truncation_compatible_origins

The existing complete proofs of cohomology, strict transitions, naturality, strict-tower
cohomology and the finite-extension assembly remain intact. No sorry is added to a
definition. Restoring pre-existing archived holes is not a new mathematical split.

## No longer needed

None. All archived imports, declarations, DAG dependencies and the Lean node attachment
are preserved. There is no withdrawal or parent-route change.

## Where the brief, the DAG or earlier work was wrong

The module is absent from lean/ because it is quarantined, not because it is unused.
The archive retained the obsolete LocallyClosedStratification identifier at its
constructibility statement. The adopted source now provides Scheme.Stratification;
this same type already occurs in IsUniformlyBoundedConstructibleAdicTower.

The initial name-only repair passed compilation and a dry run, but subsequent delivery
compiles repeatedly exceeded 60 seconds. Full-module profiling identified costly
elaboration and normalization transport. The final repair gives the existing generic
standard-localization instances local priority, keeps the universal scalar-extension
and adjunction witnesses locally irreducible, and makes transport use
only its needed categorical equations. No resource limit was raised, no module or proof
was split, and no profiler option is part of the delivered source.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
