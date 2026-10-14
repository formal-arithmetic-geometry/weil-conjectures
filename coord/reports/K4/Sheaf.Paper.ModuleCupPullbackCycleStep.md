## What changed

Restored Sheaf.Paper.ModuleCupPullbackCycleStep from the exact returned source and
restored its withdrawn cycle node. Both public theorem signatures are preserved.
The cycle theorem now uses the existing moduleCup_pullback_resolution_maps and
three fully proved private helpers: surjectivity of the computing class map,
formation of the paired cocycle, and transport of cycles under an additive cochain
map. It no longer invokes the broader moduleCup_pullback_naturality theorem.

Reproduced the reported non-module import collision, including the second collision
at the ring instance after naming the symmetric instance. Explicit names for all
anonymous local instances fixed it. The same upstream repair landed independently
in bbf7d9a0cc (Q4) while this session was working, so the experimental upstream
source edit and compiled overlays were removed. This delivery preserves the landed
moduleCupCompatibility names and changes no upstream module. The exact failing
plain import of ModuleCohomologyCupProduct passes against the published library.

Change record: coord/changes/module-cup-pullback-cycle-step.md.

## Proved and sorry left

Closed the original cycle hole in
AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_cycle_step
(lem-sc-module-cup-pullback-cycle-step) by a complete resolution-level argument.
Preserved the already proved AlgebraicGeometry.Scheme.Modules.moduleCup_pairing_exists
as an application of exists_moduleCupResolutionPairing
(lem-sc-module-cup-pairing-exists).

No sorry remains in the delivered module. No holes or split-off theorems were
added. The original split module had one hole; one is closed.

Validation: the final module compiles without warnings in 12 seconds against the
published library. A separate plain-import readback compiles in 2.2 seconds and
#print axioms reports only propext, Classical.choice and Quot.sound for both public
theorems. This verifies the actual non-module import mode of the returned failure,
in addition to module-mode compilation. The independent upstream direct importer
was checked unchanged; no adapted source is delivered.

## No longer needed

Removed proof-only import Sheaf.Paper.CechCupPullbackCompat and its use of
moduleCup_pullback_naturality (lem-sc-picard-cech-cup-pullback-compat). The resolution
proof requires none of its cover, refinement, Cech-product or Cech-comparison
steps. It uses lem-sc-module-cup-pullback-resolution-maps instead.
Replaced the unnecessarily broad public ModuleCohomologyFMapFunctorial import by
ModuleCohomologyFMap, where the pullback appearing in the signature is defined.
The functoriality theorem is not directly used in this cycle proof; it remains
an internal dependency of the existing resolution-map implementation.
The other statement imports and ModuleCupPairingExists are needed.

No unit realization is bypassed: sk-prop-av-cube has no realization attached to
this cycle node. The broad Cech node remains needed elsewhere; this report does
not claim it disappears from the entire targets closure.

## Where the brief, the DAG or earlier work was wrong

The sandbox initially held only an obsolete missing-source report. The exact
returned source was recoverable from the prior repair sandbox and the withdrawn
cycle node from the original split sandbox.

The earlier proof applied the broader pullback-naturality theorem. That theorem
is now proved in the current library by the same resolution argument, but importing
it also brings in the broader Cech proof. The new proof implements the cycle argument from the
already existing computing-resolution maps. The restored node's proof and
proof_deps now describe that argument. Its prose arrow is corrected from
f:X to X-prime to f:X-prime to X, matching the unchanged Lean signature.

The return's self-importer error was the same plain-import collision. It is now
fixed by the independently landed Q4 instance-name repair. The original pair of
public theorem signatures is retained, and there is no current source importer
of the withdrawn item. No importer adaptation or target change is needed.

## New nodes

lem-sc-module-cup-pullback-cycle-step is restored after its batch withdrawal; it
is the assigned obligation, not a new split. Its complete proof route uses the
computing resolution maps, the resolution data, and the cup-product characterization.
No new open node is introduced. Search results from LeanSearch, leanfinder, loogle and grep
are recorded in the node.

## Second reading by K4

1. Unchanged interface: PASS. The module and cycle node are absent from the
   current repository after withdrawal, so an ordinary diff reports a missing
   base file. I extracted the exact returned source from
   coord/repair-notes/Sheaf.Paper.ModuleCupPullbackCycleStep.json and diffed it
   against this delivery. The signatures of moduleCup_pairing_exists and
   moduleCup_pullback_cycle_step, including every hypothesis and the tensor
   comparison in the conclusion, are byte-identical. There are no changed
   public definitions, upstream files or target statements. The change record
   declares the restoration and public import replacement. No live source
   imports the withdrawn module or uses either restored declaration.

2. Proof and constructions: PASS. I compiled the delivered file independently
   (11.8 seconds, no warnings), then compiled a scratch copy with #print axioms
   for both public theorems and all three private helpers (11.7 seconds).
   Every declaration uses only propext, Classical.choice and Quot.sound; none
   uses sorryAx. The file has no sorry or prohibited declaration and no line
   exceeds 100 characters. pairedCycle explicitly uses the prescribed pairing
   as its underlying section, and transportedCycle explicitly uses the degree
   map; their kernel proofs follow from Leibniz and cochain commutation.
   Neither chooses arbitrary data from an unproved existence statement.
   The computing pairings are obtained inside a proof from the already proved
   resolution-map theorem. I also recompiled the plain-import collision probe
   (2.3 seconds): the previously returned upstream instance collision is gone.

3. Split statements and search: PASS. No theorem was split off and no hole was
   added. I searched with msearch.py using a bilinear-chain-pairing/cocycle query
   in leanfinder and ModuleCat.epi_iff_surjective in loogle, and searched Mathlib,
   the upstream checkout and lean/Sheaf for homology projection surjectivity,
   cycle transport and cup naturality. The surjectivity and pairing helpers in
   ModuleCohomologyCupProduct are private, hence unavailable as public lemmas.
   Mathlib supplies the epimorphism API used here. I checked degree zero
   (next 0 = 1, with no predecessor assumption), zero input cycles (bilinearity
   kills the paired cycle), and empty/zero section groups. The proof imposes no
   flatness on f and correctly uses additive cochain maps across different rings.

4. Route and pruning: PASS. I read IsModuleCupProduct, CupAcyclicResolution.class,
   CupResolutionPairing and moduleCup_pullback_resolution_maps. Surjectivity
   lifts the two original classes to the source computing pairing. Leibniz
   makes their pairing a cycle; the strict pairing equation identifies its
   transported section; the three class equations and the two cup
   characterizations finish the equality. The current library also proves
   moduleCup_pullback_naturality, but its broader Cech module brings additional
   cover and comparison imports. Keeping the direct resolution proof preserves
   the stated pruning. Every remaining public import provides symbols in the
   public signatures; PairingExists and PullbackResolutionMaps are proof-only.
   The No longer needed section accounts for the old Cech node/import and the
   broader FMapFunctorial import. sk-prop-av-cube.realized contains empty
   statement/step lists, so this change bypasses no realized unit step.
   I read [Stacks 0FKV](https://stacks.math.columbia.edu/tag/0FKV) for the
   resolution computation of cup products and
   [Stacks 01FD](https://stacks.math.columbia.edu/tag/01FD) for cohomology f-map
   comparison; the concrete pullback equations are supplied by the cited
   resolution-map node, not assumed from either source alone.

5. DAG agreement: PASS. The cycle node's proof follows the actual lifting,
   pairing/transport and class-comparison steps. Its proof_deps is exactly the
   union of the steps' uses: module cup-product characterization, resolution
   data and pullback resolution maps. Each dependency's recorded declaration
   is present and supplies the data used. The restored node has its source,
   searches, provenance, blueprint origin, chapter/unit and complete Lean
   record; it introduces no new open obligation. The unchanged pairing-existence
   alias applies the declaration already recorded by its existing node.

Changes by this reader: corrected the stale description of the broader
pullback-naturality theorem as open in the report and change record, and added this reading and its
validation evidence. No Lean proof, signature, definition or DAG record needed
repair. One original hole is closed, zero holes are added; the previously proved
pairing-existence theorem remains proved.
