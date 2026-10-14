## What changed

Recovered the withdrawn PicardModuleCechExternalPairing and
PicardExternalCechModuleRepresentatives modules and their nodes from the dedicated
repair record. The recovered proofs preserve the recorded public signatures.
Both compile together against the current shared build (32.7 s and 23.3 s).
The dry run checks the delivered modules; a separate two-import test reproduces
the previously reported batch import collision.

## Proved and sorry left

The recovered proof of
AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing closes the
assigned original hole (lem-sc-picard-module-cech-external-pairing).
AlgebraicGeometry.Scheme.Modules.picardExternalCech_moduleRepresentatives
(lem-sc-picard-external-cech-module-representatives) is also proved, using explicit
cycle transport and the refinement cochain formula. No sorry remains in either
module; no hole is added. These proofs use existing stated comparison lemmas;
this does not assert that their transitive dependencies are axiom-free.

## No longer needed

The redundant direct public import
Sheaf.AlgebraicGeometry.ModuleCohomologyCupProduct was removed in the recovered
patch; its interface is already supplied by PicardExternalCechCupBidegree.
No further node or module is pruned: all recorded proof dependencies are used.

## Where the brief, the DAG or earlier work was wrong

The brief describes an existing holed module, but the checkout contains neither
assigned module nor its node. This is a dedicated repair of a withdrawn delivery;
the repair note contains the complete two-module patch. The previous return reports
an anonymous instance collision between GlobalTensorPullbackMonoidalNormalization
and ModuleCupNaiveDerivedCompatibility in the batch probe, rather than a failed
proof step. A minimal scratch module with only imports of
Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization and
Sheaf.Paper.ModuleCupNaiveDerivedCompatibility fails in 1.0 s, reporting a duplicate
instCommRingCarrierObjOppositeOpensCarrierCarrierCommRingCatToRingedSpaceRingCatObjFunctorIsSheafGrothendieckTopologyModuleRingsOpTop_1.
Thus the batch collision remains independently of the restored Picard files.
Neither upstream module is adapted: this restoration changes no dependency they
use, so their adaptation would not meet the forced-adaptation exception.
The second reader must escalate this upstream collision; this delivery cannot
claim to have repaired the global probe. The recovered change record's earlier
claim that the collision had already been fixed was incorrect.

## New nodes

Restored lem-sc-picard-module-cech-external-pairing and
lem-sc-picard-external-cech-module-representatives from the repair record, with
unchanged statements and proof dependency routes. No new decomposition is added.
Change record: coord/changes/picard-module-cech-external-pairing-restore.md.

The first dry run rejected the restored node attribution (K4 rather than V4),
now corrected. The corrected dry run printed OK: both modules compile, and
preflight passes except for the second reading, which the launcher explicitly
reserves for the second reader. Nothing was pushed. This local result does not
resolve the independently reproduced upstream batch import collision.

## Second reading by V4

1. Interfaces: PASS. Neither delivered module nor node exists in the repository
   baseline, as the dedicated withdrawal record explains. Reconstructed both Lean
   files from the complete `diff` in that record and compared them: both are byte
   for byte identical to the recorded patch. Each public theorem signature also
   equals its node's `lean.statement` verbatim. The restoration is declared in
   `coord/changes/picard-module-cech-external-pairing-restore.md`. No target,
   definition, hypothesis or conclusion was changed in this second reading.
2. Proofs: PASS for the delivered files. Independently compiled the two modules
   in import order with lcompile.py: 38.7 s and 30.7 s, no warnings or errors.
   Scanned both complete files: no sorry, axiom, unsafe, opaque, implemented_by,
   extern or explicit sorryAx. Their private definitions construct cycle
   transports using actual isomorphisms and maps, without choosing arbitrary
   witnesses from an unproved existence theorem. In a scratch import module,
   `#print axioms` reports only propext, Classical.choice and Quot.sound for
   `picardExternalCech_moduleRepresentatives`; `picardModuleCech_externalPairing`
   additionally depends on sorryAx from existing open comparison results,
   including `cechCup_resolution_representatives`. Thus the latter is a closed
   local proof, not an axiom-free proof of its transitive closure.
3. Intermediate statements: PASS. No new statement is left sorry. Read the
   representatives theorem and all its private transport proofs in full. Its
   conclusion is strictly the Cech transport and coordinate part of the parent
   argument, with no derived comparison or covering assumption. The cycles are
   explicitly transported; homology projection naturality proves their class
   identities, and restriction composition proves the front/back cochain identity.
   Degree zero uses the same single vertex for both faces; empty index sets have
   no coordinate tuples, and zero coefficients have zero cycles, so the proof
   applies unchanged in these cases. Searched again with different wording:
   leanfinder on forgetting scalars and transporting cocycles (eight unrelated
   group-cohomology/HomComplex results), loogle on homologyπ and mapCyclesIso
   (zero results), and rg on homology/cycle transport in Mathlib and the project.
   Mathlib's existing mapCyclesIso/mapHomologyIso naturality is already used;
   no theorem replacing the scheme-specific coordinate argument was found.
4. Route and pruning: PASS. The parent first transports scalar cocycles using
   the proved representatives theorem, then uses the existing canonical Cech
   comparisons, refinement squares and resolution cup representatives. The
   adjunction uniqueness argument supplies quasi-coherence of tensor pullbacks.
   No shorter existing whole comparison theorem was found. The two public imports
   of each file supply signature notions; the parent proof-only imports are plain
   imports. The previously removed direct ModuleCohomologyCupProduct import is
   redundant through PicardExternalCechCupBidegree. No additional dependency was
   removed: every recorded proof dependency is used. Read the unit
   `dag/units/sk-prop-av-cube.json`; its statement and realized route are unchanged,
   and this comparison concerns a lower-level step only.
5. DAG: PASS. Checked the two complete node records and each dependency's Lean
   declaration. The proof descriptions follow the actual transport, coordinate,
   comparison and congruence arguments. In each record proof_deps is precisely
   the union of the steps' uses. Sources, searches, creation attribution,
   blueprint origin, chapter, unit and verbatim Lean signatures are present.
   The references to N3/K4 in proof_origin describe the historical authorship
   of the recovered patch; delivery attribution is V4.

Second-reading changes: added this review and its independent compile, axiom,
search and edge-case evidence; no Lean proof or signature required repair.
Independently recompiled scratchpad/Collision.lean: the two upstream imports
alone still fail with the duplicate instCommRingCarrierObjOppositeOpensCarrierCarrierCommRingCatToRingedSpaceRingCatObjFunctorIsSheafGrothendieckTopologyModuleRingsOpTop_1.
This is an escalation to the maintainer through the delivery report: global
batch verification requires an upstream collision repair. Neither Picard file
is involved in the minimal reproducer, and neither upstream module is adapted
without a forced dependency change. Passing this delivery's checks does not
claim that the global batch probe passes.
