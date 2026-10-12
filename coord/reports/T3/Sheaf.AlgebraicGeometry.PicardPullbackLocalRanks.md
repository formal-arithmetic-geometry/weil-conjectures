## What changed

Proved `AlgebraicGeometry.Scheme.picard_pullback_local_ranks` in
`Sheaf.AlgebraicGeometry.PicardPullbackLocalRanks`, preserving its signature and visibility.
Added proof-only imports of `Sheaf.AlgebraicGeometry.PullbackDualFiniteLocallyFree`,
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`. All original imports remain used.

Seven proved private helpers compare tensor and abstract pullback, transfer finite local
freeness and fixed rank, commute tensor pullback with duals, prove equality of dual ranks
from local generators, and explicitly transport a presentation across a base change.
The main proof identifies the two direct images using the existing unit theorem, chooses
one finite local frame, and transfers rank to all three modules. No new module object is
chosen from an unproved existence assertion: the relevant module is explicitly h^*N;
the comparisons are isomorphisms between already constructed modules.

Updated only `proof`, `proof_deps`, and `proof_origin` of
`lem-sc-picard-pullback-local-ranks`. The additional dual-pullback node is used as a tool:
it supplies the general finite-locally-free dual comparison missing from this unit's
existing interfaces. The cube unit's `realized` lists are empty and no unit step is bypassed.
Read Stacks Tags [0BDP](https://stacks.math.columbia.edu/tag/0BDP) (the projection-formula
paragraph) and [01E8](https://stacks.math.columbia.edu/tag/01E8). The proof implements their
local-frame argument without requiring the unused properness/flatness hypotheses of the
larger representability result. Empty bases have no point to check; zero rank uses Fin 0
throughout and requires no nontriviality hypothesis.

Local single-file compilation passed with no errors or warnings in 20.8 seconds.
An early version imported the broad `FiniteDescent` module and initially compiled in
29.5 seconds, but subsequent checks timed out. Removing that import and using a proved
private finite-frame helper resolved the timeout without splitting files or proofs.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.picard_pullback_local_ranks`
(node `lem-sc-picard-pullback-local-ranks`). No `sorry` remains in the delivered module;
no holes or axioms were added. This is a proof from existing declarations, not a decomposition.

The imported existing theorem
`AlgebraicGeometry.Scheme.isIso_tensorPullback_unit_of_finiteLocallyFree`
(node `lem-sc-finite-locally-free-tensor-unit`) still contains `sorry` outside this delivery.
At second reading, `#print axioms` for the dual comparison and all six other private
helpers showed only `propext`, `Classical.choice`, and `Quot.sound`. The main theorem
additionally uses `sorryAx` through the existing unit theorem. Therefore the theorem
is not claimed axiom-free in its transitive dependency closure.

## No longer needed

No original import, planned node, or planned module was removed.
Removed the exploratory proof import
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`: only its elementary
finite-local-freeness pullback argument was needed, now a proved private helper using
local frames, restriction/pullback composition, and pullbackFreeIso. This avoids importing
its fpqc descent infrastructure. It was not in the original module, so no baseline
closure pruning is claimed.
All three original proof dependencies remain used. No additional modules are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The plan's assertion that pullback commutes with finite-locally-free duals already has a
usable library theorem (`Modules.nonempty_pullback_dual_iso_of_isFiniteLocallyFree`), but
its node was absent from this item's proof dependencies. It is now recorded explicitly.
No statement, definition, public import, or downstream module needed correction.

Searches ran through msearch: LeanFinder returned rank-at-stalk and algebraic dual-rank
results; Loogle did not recognize the custom fixed-rank predicate; grep found abstract
pullback-free results. Direct searches of both library roots found the dual comparison,
finite-local-freeness and fixed-rank pullback instances, local-frame existence, and the
finite-free internal-dual isomorphism. These existing results sufficed without new holes.

## Second reading by T3

1. PASS: compared the complete delivered module with the repository version using
   `diff -u`. The existing theorem signature, visibility, docstring, definitions used
   by its statement, and all public imports are byte for byte unchanged. The only Lean
   additions are two proof-only imports, seven private helpers, and the theorem proof.
   No change record or forced adaptation is required.
2. PASS: local compilation completed without errors or warnings in 17.2 seconds.
   A scratch copy with `#print axioms` for every private helper and the public theorem
   compiled in 18.9 seconds. All helpers use only the three permitted standard axioms;
   the theorem additionally uses the documented upstream `sorryAx`. The delivery has
   no `sorry`, forbidden declaration, hollow definition, or new arbitrary module witness.
   The chosen comparisons relate explicitly constructed objects; the local frame theorem
   itself has only standard axioms.
3. PASS: no statement was split off and no new hole or public statement was added.
   Checked the private finite-frame, dual-rank, and presentation transports against their
   actual types. Rank zero uses the empty finite frame; an empty base supplies no point;
   an empty inverse-image open does not require a nontrivial coefficient ring. Independent
   searches used Loogle `CategoryTheory.Adjunction.leftAdjointUniq`, msearch grep
   `homObjFreeUnitIso|overHomObjIso|leftAdjointUniq`, and direct library searches for
   dual/rank and pullback/local-freeness combinations. They confirmed the comparison and
   free-dual APIs already used. The general finite-local-freeness pullback instance is
   in the broader FiniteDescent module; the small proved helper avoids that extra import.
4. PASS: read the proof from the direct-image identifications down to local frames and
   checked the argument against the projection-formula paragraph of
   [Stacks 0BDP](https://stacks.math.columbia.edu/tag/0BDP) and the local finite-free
   calculation of [Stacks 01E8](https://stacks.math.columbia.edu/tag/01E8).
   Both added imports are proof-only and used; original signature imports are appropriate.
   Every original proof dependency remains used, so `No longer needed` correctly claims
   no baseline pruning. Read `dag/units/sk-prop-av-cube.json`: its unchanged `realized`
   lists are empty. The original projection-formula/local-frame route is retained, and
   the added dual-pullback result is a general tool rather than a replacement unit step.
5. PASS: compared the node JSON with the repository version. Only `proof`, `proof_deps`,
   and `proof_origin` differ. The three proof steps describe the actual Lean transports,
   their `uses` union is exactly `proof_deps`, and the additional existing dual-pullback
   node records the imported declaration. There are no new nodes to validate.

Changed only this report: corrected the earlier claim that the dual-comparison dependency
still uses `sorryAx`, using the independent axiom output, and appended this second reading.
The Lean proof and node required no repair. Closed one original hole, added zero holes;
no split-off statement and no pruned baseline module.
