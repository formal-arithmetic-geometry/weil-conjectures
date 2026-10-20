## What changed

Restored Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback from its
quarantine archive. Replaced the withdrawn Sheaf derived-pullback public import
with the canonical WeilConjectures module, selected the upstream KFlatResolution
and BoundedAboveFlatRingedSpaceKFlat proof imports, and changed the private
pullback_Q_iso hypothesis to CochainComplex.IsKFlatTensor. Replaced the broad
QuasicoherentKernel proof import with the module-sheaf API actually used.

The complete archived proof is retained: transport the model through the open
site equivalence, compute pullback using the bounded-above flat criterion and
K-flat counit, then compose the open-restriction comparison. Every proof body
and the public theorem signature are unchanged. The existing node attachment,
proof steps and dependency IDs are preserved; proof_origin records the repair.
The unit route is preserved. No source-library or consumer module is modified.

Validation: the final item compiles without warnings in 14.4 seconds through
lcompile.py. A separate probe applies the restored theorem at the archived
public signature. The axiom check reports only propext, Classical.choice and
Quot.sound. Empty inverse images and zero ranks retain the archived argument:
ht supplies membership in the inverse image, and pullback preserves zero/free
objects without a positivity assumption.

Change record: coord/changes/T2-finite-free-residue-model-pullback-restoration.md.

## Proved and sorry left

AlgebraicGeometry.Scheme.finiteFreeResidueModel_pullback is fully proved, as are
its three private helpers pullback_Q_iso, openRestriction_iso and free_flat.
The assigned item is a quarantine repair with zero original direct sorries.
Holes closed: none (0). Holes added: none (0). Sorries left: none (0).
No decomposition and no split-off results. The public theorem has no reachable
sorryAx according to the independent axiom probe.

## No longer needed

Removed the direct imports Sheaf.AlgebraicGeometry.DerivedPullback,
Sheaf.Algebra.Homology.KFlatResolution and
Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat in favor of their adopted
upstream counterparts. Removed
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel: its kernel and
quasi-coherence theory is unused; the smaller module-sheaf API supplies the free
and unit comparison isomorphisms. These are import replacements, not withdrawals
of those modules from the library. No DAG dependency or unit step is pruned.
The quarantined item, its parent and their dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

This item has no direct sorry in its archive; its actual assignment is the
recorded rework import collision. The old private helper also used the legacy
IsAcyclicTensorKFlat API, whereas the canonical derivedPullback_spec expects
IsKFlatTensor. The upstream criterion and resolution fit the retained proof.

The sole Lean consumer and DAG parent is the quarantined
Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel. Its unchanged source
was tested against this restoration, but compilation stops at its own preexisting
PerfectComplex collision: Sheaf.AlgebraicGeometry.PerfectComplex reintroduces
AlgebraicGeometry.Scheme.IsPerfect already supplied by the upstream module.
This failure precedes its use of finiteFreeResidueModel_pullback and is a separate
rework item; this packet does not expand into that repair. The consumer's theorem
application still matches the restored public signature. The quarantine archives
are preserved. No mathematical statement dispute or target change is introduced.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
