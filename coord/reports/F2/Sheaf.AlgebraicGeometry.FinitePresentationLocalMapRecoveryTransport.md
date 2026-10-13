## What changed

Proved the unchanged `AlgebraicGeometry.finitePresentation_local_maps_recovery_transport`
by substituting its supplied canonicality equalities, applying recovery composition,
conjugating by the comparison z, and cancelling with canonical tensor associativity.
The original declaration signature is byte for byte unchanged.

Added `LocalMapRecoveryComposition`, `OpenCoverTensorPullbackComposition`, and
`TensorPullbackCompositionAssociativity`. The chart comparison is constructed explicitly
from pullbackRightPullbackFstIso and pullback.congrHom, with both projections proved.
No definition or existing statement is changed. The two unchanged dependency files
previously copied into the sandbox were removed from the delivery set.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.finitePresentation_local_maps_recovery_transport`
(node lem-pc-fp-local-map-recovery-transport).

New proved declarations:
- `AlgebraicGeometry.localMapRecovery_composition`
  (node lem-pc-local-map-recovery-composition).
- `AlgebraicGeometry.Scheme.Modules.tensorPullbackCompositionIso_associativity`
  (node lem-pc-tensor-pullback-composition-associativity).

Added hole: `AlgebraicGeometry.Scheme.Modules.openCoverTensorPullbackComparison_composition`
(node lem-pc-open-cover-tensor-pullback-composition). Its docstring contains the
complete mate-calculus proof. This is a strictly smaller coherence square with no
local family, map delta, or recovery hypothesis. There is no sorry in the item's module.

Removed the unproved `AlgebraicGeometry.localMapRecovery_transport_core` restatement
and its proposed new node, rather than delivering it as progress. Closed the proposed
`AlgebraicGeometry.localMapRecovery_composition` hole during second reading.
Against the repository baseline this delivery closes one hole and adds one: it is a
decomposition, with net zero holes closed, not a completed proof of the import closure.
Existing imported holes are not claimed closed.

## No longer needed

Removed the item's redundant direct public import
`Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison`; the same module remains
publicly reachable through `LocalMapRecovery` and `LocalMapPullbackFamily`, and its
comparison is used by the naturality calculation. No library module becomes unreachable.

Of the old proof_deps, `lem-pc-module-pullback-adjunction` is no longer a direct
proof dependency of the item's theorem: the new proof uses the two coherence/recovery
lemmas instead. The adjunction node remains needed below them. The old comparison
definition nodes remain used or occur in the signature. Removed unused private mate
helpers from the square module. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first delivery draft delegated the main statement to an unproved core theorem
after only substituting functor and isomorphism equalities. That is not an acceptable
reduction. The second reading removed it and implemented the advertised combination
of the two strictly smaller intermediate lemmas. The earlier report also incorrectly
suggested that only the core theorem remained open; it actually contained three holes.
The recovery-composition hole is now closed and only the comparison square remains.

## New nodes

`lem-pc-local-map-recovery-composition`: recovery for two successive pullbacks of
arbitrary modules, proved using chart construction, naturality, and the restriction square.

`lem-pc-open-cover-tensor-pullback-composition`: the restriction comparison square,
the sole new open theorem. Its statement is independent of recovery and is strictly
one coherence step in the original argument.

`lem-pc-tensor-pullback-composition-associativity`: canonical tensor comparisons
associate, proved by Mathlib's Adjunction.leftAdjointCompIso_assoc and sectionwise
pushforward coherence. Import and local proof-command changes are recorded in
`coord/changes/finitePresentation_local_maps_recovery_transport_imports.md`;
there is no statement or definition change.

## Second reading by F2

1. **Interfaces: pass after repair.** Compared every sandbox Lean file with the
   repository version. The two unchanged copied dependencies were removed. For the
   existing item, the full original theorem signature is byte for byte unchanged;
   the declaration comparison reports no statement changes. There are no definition
   changes. Import removal and local proof-command changes have the explicit change
   record named above. Effective public exports remain available transitively.
2. **Proofs: pass with the stated remaining obligation.** Compiled all four modules
   through lcompile.py in import order, and compiled scratch copies with #print axioms.
   Tensor associativity has only propext, Classical.choice and Quot.sound. The main
   theorem and recovery composition have those axioms and sorryAx, via the one
   documented square. All remaining sorry occurrences consist of exactly the named
   public square theorem with proof `by sorry`; no prohibited declarations or hollow
   definitions occur. The chart isomorphism is constructed explicitly, not chosen
   from an unproved mere-existence assertion. Files stay below the 60-second limit;
   the slowest observed final compile was about 34 seconds.
3. **Split statements: pass after repair.** Removed the core-transport restatement
   and its node. Proved the proposed recovery-composition obligation by constructing
   the chart comparison and using the smaller square. The only remaining split
   statement asserts equality of two canonical comparison paths, with neither a
   recovery hypothesis nor an arbitrary coefficient morphism. Both paths have the
   same source and target. Its docstring gives the mate proof and its node matches
   the full signature. Checked identity maps, zero modules and maps, empty covers
   and empty charts: the identities remain categorical identities, and universal
   quantification over an empty index type is vacuous. Independently searched Loogle
   for NatIso.naturality_1, Lean Finder for pullback/restriction compatibility, and
   grep for pullback_assoc, pullbackComp and conjugateEquiv_whisker; searched the
   project's Sheaf and WeilConjectures sources by comparison and recovery names.
   Mathlib supplies naturality, mates and ordinary associativity, but no exact
   mixed tensor/ordinary cover square. No duplicate public result was introduced.
4. **Route and pruning: pass.** The main proof now combines the two strictly smaller
   results using naturality and the two explicit inverse-cancellation identities.
   Tensor associativity uses Mathlib's proved Adjunction.leftAdjointCompIso_assoc.
   Every remaining direct import supplies a signature or an invoked proof lemma;
   the redundant comparison import and unused private mate calculations were
   removed. The old proof_deps are accounted for under No longer needed. The unit
   sk-thm-picard-semicon has empty realized statement/step lists; no realized route
   is bypassed, and no library module is claimed globally pruned.
5. **Nodes: pass after repair.** Read all delivered node records against the Lean.
   Updated the recovery-composition proof to describe the actual chart/naturality
   calculation and updated dependency unions. The main node describes substitution,
   recovery composition, conjugation and associativity exactly as written. New nodes
   have source, full statement, proof steps, searches, creation metadata, blueprint,
   unit/chapter and Lean records. Existing statement data is unchanged.

Second reading changes: removed the restatement and its node; wrote the actual main
reduction; proved recovery composition; made chart construction private; removed
unused square helpers and unchanged copied files; pruned the redundant direct import;
added its change record; corrected the report and node proof dependencies. This is a
decomposition with one original hole closed and one strictly smaller hole added.
