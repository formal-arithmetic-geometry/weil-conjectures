## What changed

Proved `Algebra.stonean_cover_second_stage` in
`Sheaf.RingTheory.StoneanCoverSecondStage`, preserving its complete statement,
all public definitions, all public imports, and the finite-stage normalization.
Only private, proved helpers were added. No other Lean module changes.

The comparison is constructed from two surjections out of `LocallyConstant S C`.
The first uses the existing colimiting discrete-quotient cocone, followed by the
coordinate restriction maps. The second is the structure map to the existing
canonical graph restriction. An explicit kernel calculation identifies the two
quotients: eventual vanishing supplies a clopen-neighbourhood idempotent, and
refinement makes its locally constant values constant on each part. The algebra
first isomorphism theorem then gives the normalized comparison.

The other clauses use the proved upstream `PullbackProfinite` API: its pullback,
local-ring bijectivity, faithful flatness, closed-point formula and component
homeomorphism. Strict henselianity transports through the canonical local maps.
The proved `Algebra.isIndPrincipalZariski_of_bijective_localRingHom` upgrades the
upstream ind-Zariski notion to the exact finite-principal-product predicate in the
statement. Its hypothesis is used only after w-locality of the target is proved.
The dependency imports and node proof were updated accordingly.

No nonempty-space assumption is introduced. The empty partition is retained;
all coordinatewise constructions and the kernel proof apply to it. The argument
also handles the zero ring and arbitrary noninjective surjective `f`.

## Proved and sorry left

Closed the sole original hole: `Algebra.stonean_cover_second_stage`
(node `det-pe-wc-cover-second-stage`). Proved 1 of 1 original sorries.
Added 0 sorries; split off 0 statements. No sorry remains in the delivered module.
All private helpers have complete proofs.

## No longer needed

Removed these proof-only imports:

- `Sheaf.Topology.WLocalComponents`
- `Sheaf.Topology.StoneanCover`
- `Sheaf.RingTheory.IndEtaleStability`
- `WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`
- `Sheaf.RingTheory.IndEtaleUniverseTransport`

The parent proof no longer needs these old proof dependencies:

- `lem-pe-clopen-restriction-canonical-localization`
  (`Sheaf.RingTheory.ClopenRestrictionCanonicalLocalization`): the actual upstream
  restriction colimit already has surjectivity; the zero criterion is proved
  directly by Mathlib's filtered-colimit equality theorem.
- `lem-pe-partition-restriction-ind-zariski`
  (`Sheaf.RingTheory.PartitionRestrictionIndZariski`): the comparison is proved by
  equality of kernels, and the exact principal presentation follows from the
  already proved generic local-ring theorem.
- `lem-pe-profinite-partition-incidence-limit`
  (`Sheaf.Topology.ProfinitePartitionIncidenceLimit`): the graph model already has
  the canonical pullback homeomorphism.
- `lem-a1-filtered-spectrum-topological-limit`
  (`Sheaf.Topology.FilteredSpectrumTopologicalLimit`): no general spectrum-limit
  theorem is needed to compare these two quotients.
- `lem-weil-pbc-filtered-colimit-localization-at-prime`
  (`WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`): the
  upstream ind-Zariski API proves the canonical local-ring bijectivity directly.
- `lem-weil-pbc-finite-affine-coproduct-spectrum`: the proof never computes a
  finite-product spectrum.
- `lem-weil-pbc-product-prime-localization`: canonical local-ring bijectivity is
  used directly.
- `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat`: the upstream
  `PullbackProfinite.faithfullyFlat` theorem packages this argument already.
- `lem-weil-pbc-ind-etale-stability`
  (`Sheaf.RingTheory.IndEtaleStability`): the existing proved upstream instances
  provide ind-etaleness.

Removed the three obsolete top-level `tool_uses` approvals for
`lem-weil-pbc-ind-etale-stability`,
`lem-weil-pbc-filtered-colimit-localization-at-prime`, and
`lem-a1-filtered-spectrum-topological-limit`.

These are dependencies pruned from this proof, not requests to delete any source
module. Other consumers and their unit routes keep whatever they still require.
The existing partition-definition node remains attached, unchanged.

## Where the brief, the DAG or earlier work was wrong

The current blueprint update of 2026-10-23 uses the graph-restriction ring instead
of requiring a partition-colimit construction as its primary model. Its Lean
implementation and geometric results are already proved upstream. The older Lean
statement additionally requires the normalized comparison with the partition
colimit. That comparison is still used by
`Sheaf.Paper.WStrictCommonComponentHypercovers`, so it was proved and preserved,
not removed. The new DAG proof follows the current graph argument and records the
additional quotient-kernel comparison explicitly. The unit's finite-quotient and
idempotent-localization construction is retained in the upstream graph model and
in the comparison proof. No target, public signature or definition changed.

Searches through `msearch.py` (Lean Finder, Loogle and grep), and source searches in
Mathlib, Sheaf and WeilConjectures located the existing discrete-quotient colimit
and graph APIs. No additional public lemmas or new nodes were necessary.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
