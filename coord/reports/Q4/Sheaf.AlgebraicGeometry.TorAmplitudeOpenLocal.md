## What changed

Restored Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal from its quarantined assignment as
an operational compatibility module. It publicly imports the existing, fully proved
WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal, and separately imports all of that
module to retain the private-helper interface for import-all consumers. This removes the
recorded duplicate derivedPullback import failure and the next duplicate tensor-vanishing
failure, while reusing the exact existing public theorem and its complete proof.

Updated only lean.module, lean.file and lean.note of lem-pc-tor-amplitude-open-local to name
the actual canonical declaration. The public signature is byte-identical in the archive,
the DAG and the upstream module. All statement and proof dependencies are preserved.
No source-library file, target, consumer, mathematical statement or definition is edited.
The quarantine archive is untouched; this is restoration, not module withdrawal.

Change record: coord/changes/Q4-tor-amplitude-open-local-restoration.md.

Validation: lcompile.py compiled the restored module in 1.4 seconds. A separate consumer,
compiled in the same two-file invocation against the sandbox artifact, proved an example
with exactly the archived public signature and imported the five existing source consumer
modules without duplicate-name failures. It checked all five private helpers, including
the open_pullback_restriction_iso used by the archived PerfectDegreeZeroFibreCriterion.
The consumer compiled in 1.7 seconds. The axiom check of
AlgebraicGeometry.torAmplitude_of_open_neighbourhoods reports precisely propext,
Classical.choice and Quot.sound. The probe lives only in scratchpad, outside the packet.

## Proved and sorry left

Definition/import repair with zero direct holes before and after.
AlgebraicGeometry.torAmplitude_of_open_neighbourhoods already has a complete source proof;
this delivery restores access to it. Closed holes: none (0 of 0). Added holes: none.
Sorry left in the item or added modules: none. No decomposition and no new theorem.
The standard-axiom check also excludes transitive sorry dependence of the public theorem.

## No longer needed

The restored compatibility module replaces these archived direct imports by the canonical
TorAmplitudeOpenLocal import:

- WeilConjectures.AlgebraicGeometry.LocallyFiniteTorDimension
- Sheaf.Algebra.Homology.KFlatResolution
- Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
- Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
- WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Sheaf.AlgebraicGeometry.DerivedPullback
- Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
- Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
- WeilConjectures.AlgebraicGeometry.OpenRestrictionTotalTensor
- Sheaf.AlgebraicGeometry.SheafZeroStalks

The canonical proof still needs the corresponding K-flat, tensor-comparison, restriction
and local detection results. The old direct SheafZeroStalks import was unused: the proof
uses the source isZero_of_iSup_eq_top cover criterion. No mathematical proof dependency
or node is withdrawn. No module is deleted or claimed pruned; the remaining Sheaf twins
may still have consumers and their independent retirement items are outside this repair.

## Where the brief, the DAG or earlier work was wrong

The rework row identifies an import conflict rather than a missing proof. Changing just
the retired derived-pullback import is insufficient: tensor vanishing has also migrated
upstream. The byte-identical public theorem and complete proof already exist in the source
library, while this node still pointed at the quarantined duplicate.

The retirement census flags changed private K-flat helper signatures (IsAcyclicTensorKFlat
became IsKFlatTensor). Current source consumers already use the current API. The sole
archived direct consumer of this Sheaf path uses open_pullback_restriction_iso, whose
signature remains identical; the separate import all retains access to it. No consumer
adaptation is forced. The module continues to represent lem-pc-tor-amplitude-open-local,
and its K-flat/open-cover proof and unit route remain in force.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
