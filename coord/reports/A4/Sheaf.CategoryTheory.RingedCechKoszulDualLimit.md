## What changed

Restored lean/Sheaf/CategoryTheory/RingedCechKoszulDualLimit.lean from its exact
quarantine archive. Replaced the retired public Sheaf telescope import with
WeilConjectures.Algebra.Homology.TelescopeColimit and the occurrence of
CochainComplex.telescopeShiftColimit with the source name telescopeColimitShift.
The old name was an abbreviation of that exact construction. Updated the existing
node's Lean statement and note, preserving its mathematical statement, dependencies
and proof route. The complete normalized comparison structure and its proofs remain.
Change record: coord/changes/A4-ringed-cech-koszul-dual-limit-restoration.md.

The restored module compiles cleanly via lcompile.py in 11.7 seconds. The original
failure in coord/rework.tsv was an unknown-identifier error for the retired shift
and its unexported telescopeToColimit. No additional proofs were required.

## Proved and sorry left

Assigned repair completed. Original holes: 0; holes closed: 0; holes added: 0;
remaining holes: 0. No declaration contains sorry. In particular, the existing
CategoryTheory.exists_ringed_koszul_cech_comparison and
CategoryTheory.ringed_cech_koszul_dual_limit proofs are preserved, as are all
private helpers. This is an API restoration, not a new proof or a decomposition.

## No longer needed

Removed the retired import Sheaf.Algebra.Homology.TelescopeColimit; its proved
source replacement supplies the identical telescope API directly. No nodes or
mathematical dependencies are pruned: lem-pc-complex-hocolim-colimit remains used.
All other imports remain. No modules withdrawn and no archive deleted.

## Where the brief, the DAG or earlier work was wrong

The module was absent from lean/ because it was quarantined, not withdrawn. Its
zero-hole archive still used the retired telescopeShiftColimit alias. Followed the
explicit restoration substitutions in coord/changes/retire-telescope-colimit-a2.md.
The old DAG Lean attachment contained the retired spelling and now records the
canonical one; the mathematical statement has not changed. Three quarantined
consumers retain their files and dependencies and need no source adaptation.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
