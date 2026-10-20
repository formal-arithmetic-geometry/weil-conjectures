## What changed

Completed the active-source retirement listed in coord/retire-items.tsv, row
Sheaf.Algebra.Homology.TelescopeColimit, following the human's 2026-10-20 hand-off.
The item already re-exported the fully proved upstream telescope comparison and
contained only the old shift-name abbreviation. Withdraw that wrapper through
deleted.txt. Both current direct consumers now privately import
WeilConjectures.Algebra.Homology.TelescopeColimit. Their statements, definitions,
proofs and all other imports are unchanged.

The comparison node already attaches to the upstream theorem. Update its Lean
note to record direct use of that theorem and the canonical shift name. Its
statement, proof steps, proof dependencies and unit route are unchanged.

Both changed consumers compile: RingedCechKoszulHomLimitComparison (2.7 seconds)
and Sites.ContractibleDerivedSectionsTensor (30.4 seconds). A separate scratch
probe checks the direct-sum formula by reflexivity and applies the upstream
comparison with both canonicality equations. The source theorem's axiom probe
is recorded in the change record. No source-library module or target is changed.

## Proved and sorry left

Item baseline: zero sorries. Holes closed: zero. Holes added: zero. Split off: zero.
This is retirement of a proved wrapper, not a new mathematical proof.

Unchanged holes in the two adapted consumers:
- CategoryTheory.exists_ringed_cech_koszul_hom_limit_comparison.
- AlgebraicGeometry.contractible_derived_sections_tensor.

No new nodes or proof holes are introduced.

## No longer needed

Retire Sheaf.Algebra.Homology.TelescopeColimit and replace its two active import
edges with direct imports of WeilConjectures.Algebra.Homology.TelescopeColimit.
The former CochainComplex.telescopeShiftColimit abbreviation has no active Lean
users. Its upstream name is CochainComplex.telescopeColimitShift, with exactly
the same formula. CochainComplex.telescopeToColimit and
CochainComplex.quasiIso_telescopeColimit continue to come from the upstream module.

No mathematical dependency nodes are pruned: monicity of one minus shift and the
short-exact cone comparison remain dependencies of the preserved upstream proof.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief is stale for this item: the queue now assigns retirement,
and the 2026-10-20 M4 consolidation already reduced the item to a re-export and an
abbreviation. It has no proof hole to close. The retirement inventory also lists
Sheaf.Algebra.Homology.TruncationTelescope, already absent from active sources;
its source twin already imports the source telescope directly.

The remaining inventory consumer, Sheaf.CategoryTheory.RingedCechKoszulDualLimit,
is quarantined under its current coord/rework.tsv row. Preserve that archive and
its Lean attachment and all dependency nodes. It is not restored or withdrawn by
this packet. Its future rework must replace the old public import by the source
import and rename telescopeShiftColimit to telescopeColimitShift. The exact
archival adaptation is recorded in coord/changes/retire-telescope-colimit-a2.md;
this packet does not claim that quarantined module compiles. Its parent still
needs lem-pc-complex-hocolim-colimit, which remains attached to the proved source
theorem with the complete original conclusion.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
