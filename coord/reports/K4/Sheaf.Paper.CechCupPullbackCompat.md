## What changed

Closed the two holes in the initially dispatched snapshot using the existing
moduleCup_coefficient_resolution_maps and moduleCup_pullback_resolution_maps.
The private helpers prove surjectivity of computing resolution classes, construct
paired cycles by Leibniz, and transport cycles across additive cochain maps with
different scalar rings. The product characterizations and the three class equations
then give both naturalities. All existing signatures remain unchanged.

During this work the read-only repository refreshed to the Y3 landing at
2026-10-14 05:32 UTC (ledger landing 20261014T053244-L-2011935), which already
closes both dispatched holes. The sandbox retains the proofs of the original
snapshot, but these are duplicate progress relative to the refreshed baseline.

## Proved and sorry left

Closed in the original snapshot:
- AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality.
- AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality.

No sorry remains in the item's module; no hole was added. The proofs use existing
resolution-map declarations, whose dependencies remain separate library work.
Final single-file compilation succeeded without warnings in 39.5 seconds.
The maxHeartbeats explanatory comment fixes the initial style warning.
The earlier attempt reported zero net new progress after a baseline refresh;
this session does not claim additional holes beyond the two original closures.
The current delivery dry run accepts the preserved proof and node changes.

## No longer needed

Second reading removed the proof-only import
Sheaf.Paper.CechComparisonMapNaturality and the old proof dependency
lem-sc-cech-comparison-map-naturality. The composite comparison square now uses
cechRefinement_comparison_square directly, without constructing unrelated canonical
comparisons or auxiliary cup products. No other old proof dependency is omitted.
The remaining public imports supply names in existing signatures; the two added
resolution-map imports are proof-only. No unit route is bypassed. This removes a
direct module dependency; it does not claim the module leaves the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The dispatched item became stale while the session was running: Y3's landing
closed both remaining holes. This is a dispatch/baseline race, not a mathematical
obstruction. The existing resolution-map signatures fit both naturality arguments.
No new nodes or statement corrections are needed. The copied node already records
the computing-resolution route followed by these proofs.

Revalidation on 2026-10-14: deliver3.py K4 Sheaf.Paper.CechCupPullbackCompat
--no-push printed OK (dry run), commit 175d0722b6: compilation and preflight
passed except for the second reading, which the independent second reader writes.
This supersedes the earlier attempt's "FAILED: nothing is proved" result.
No push or delivery was attempted. The existing proof was inspected; no Lean
statement or proof was changed in this revalidation session.

## Second reading by K4

1. PASS: diffed the only delivered Lean module against the read-only repository.
   Every existing declaration signature is byte-for-byte unchanged; no definition,
   public import, target statement or existing docstring changed. The only additions
   are three private, fully proved cycle helpers and two proof-only imports. No
   statement-change record is necessary.
2. PASS: compiled the complete module and a scratch copy with #print axioms for
   all seven public theorems. The final scratch compile passed without warnings
   in 37.2 seconds. No sorry, axiom, unsafe, opaque, implemented_by or extern occurs
   in the delivered source, and every helper definition constructs its data.
   moduleCup_coefficient_naturality, cechRefinement_coefficient_naturality,
   cechCup_coefficient_naturality and cechCup_refinement_naturality use only propext,
   Classical.choice and Quot.sound. cechCupPullbackCompat,
   moduleCup_pullback_naturality and cechRefinement_composition_naturality additionally
   use sorryAx through existing open dependencies. They are local hole closures,
   not claims that the full target import closure is proved.
3. PASS: no statements were split off and no holes were added. Read both existing
   resolution-map signatures and the resolution/class/product definitions. The
   class-map surjectivity uses the epi cycle projection and two isomorphisms;
   Leibniz constructs the paired cycle; the additive chain-map equation transports
   cycles between different scalar rings without an invalid linearity assumption.
   These arguments cover degree zero, zero cycles and empty schemes. Searched
   lean/Sheaf and upstream homology code with class/surjectivity and cycle-transport
   terms: equivalent resolution helpers exist only privately in other modules,
   so cannot replace these local helpers. No new public theorem or new node exists.
4. PASS AFTER REPAIR: read the whole module from the top down. Replaced the
   composition proof's auxiliary comparison/product existence detour by the
   existing cechRefinement_comparison_square theorem. Removed the resulting unused
   CechComparisonMapNaturality import. All remaining imports supply signatures or
   proofs. No unit-level argument is bypassed. The unit sk-prop-av-cube currently
   has empty realized.statement and realized.steps entries in the repository;
   this pre-existing omission is reported here, and this delivery does not alter
   the read-only unit record or its route.
5. PASS AFTER REPAIR: compared node JSON semantically. The proof, proof_deps and
   proof_origin describe exactly the computing-resolution and direct comparison
   routes now used; proof_deps is the union of the proof steps' uses. No new nodes
   need auditing. Restored the repository's reviewed_proof metadata rather than
   delivering the sandbox's copied Y3 review metadata (outside worker-owned fields).

Second reading changed only the composition proof, removed its unused proof import,
restored non-owned node review metadata, and corrected/extended this report. The two
original dispatched holes closed are moduleCup_coefficient_naturality and
moduleCup_pullback_naturality; zero holes were added and zero statements split off.
The repository snapshot read here still contains these two sorry bodies, despite
its copied historical landing information. Delivery tools determine the current
server baseline and ledger accounting; no duplicate progress is claimed.
