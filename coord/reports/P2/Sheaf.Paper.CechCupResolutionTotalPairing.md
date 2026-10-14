## What changed

Restored `Sheaf.Paper.CechCupResolutionTotalPairing` and
`Sheaf.Paper.CechCupResolutionBetaClassPairing`, absent in the repository baseline,
with their two DAG nodes. No existing Lean statement or definition is changed.
The total theorem constructs a bilinear map by transporting the uniquely
characterized sheaf cup product, proves its alpha formula directly, and reduces
only its beta formula to the named beta compatibility theorem. The beta import
is private (`import`); the two public imports supply types in the signatures.

## Proved and sorry left

Proof body completed: `AlgebraicGeometry.Scheme.Modules.cupCechResolution_total_pairing`
(node `lem-sc-cech-cup-resolution-total-pairing`). Its alpha branch is proved using
`alpha_class` and `IsModuleCupProduct`; its beta branch uses the remaining theorem.

Hole added/restored: `AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing`
(node `lem-sc-cech-cup-resolution-beta-class-pairing`), whose proof is exactly `by sorry`.
No other delivered declaration contains sorry. No definition is added.

Holes closed relative to the current repository baseline: none, because both
modules were absent after rollback. This is a restoration and decomposition,
not an axiom-free proof or a claimed positive ledger net. The total theorem still
transitively depends on sorryAx (including open upstream cup-product obligations).
The ledger determines closure reach and net progress against its pinned baselines.

## No longer needed

None. Both baseline module/node files are absent, so there is no old proof_deps
list or baseline import to prune. All delivered imports are needed for signature
objects or the beta proof. No unit-level dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The baseline omitted both restored modules and nodes after the earlier rollback.
The previous report's wording "proved with no sorry" described only the upper
proof body; it did not establish an axiom-free theorem or a positive ledger net.
The restored nodes also carried old review stamps from a different delivery;
those stamps have been removed rather than claimed as a review of this restoration.

## New nodes

`lem-sc-cech-cup-resolution-total-pairing`: restored total homology pairing
statement, with both axis formulas and its explicit transport proof.

`lem-sc-cech-cup-resolution-beta-class-pairing`: restored beta-axis compatibility
obligation. It has no existence claim for a total pairing and no alpha formula;
it is the augmentation-axis part of the argument, not a renamed whole target.
Its docstring gives the signed cochain construction, descent, alpha identification
and beta calculation, including why a covering assumption is not needed when the
comparison data explicitly supply alpha quasi-isomorphisms.

Change record: `coord/changes/CechCupResolutionTotalPairing-restored.md`.

## Second reading by P2

1. Compared each delivered Lean module with the repository using diff: both are
   additions because both baseline files are absent. The restoration is declared
   in the change record, now containing both new signatures verbatim. Checked
   both signatures against their DAG records; they agree. No existing target,
   declaration, definition, hypothesis or conclusion was edited. Verdict: pass.

2. Compiled both modules with lcompile.py --all, in import order, without errors
   or warnings. Compiled scratch copies with #print axioms for both declarations:
   both use propext, Classical.choice, Quot.sound and sorryAx.
   The only local hole is the named beta theorem. No axiom, unsafe, opaque,
   implemented_by, extern, hollow definition or arbitrary data choice occurs.
   The selected cup is constrained by a uniqueness characterization; the map t
   is explicit linear-map composition inside an existential proof. Verdict: pass
   as a partial decomposition, not as an axiom-free proof.

3. Read the beta statement against CupResolutionPairing and all comparison fields.
   Checked degrees zero, zero inputs, repeated indices and empty index families:
   the signed cochain formula gives sign one on each axis, and zero inputs give
   zero by bilinearity. Empty families with comparison data force total homology
   to be zero. No covering hypothesis is needed for this sectionwise calculation;
   invertibility of alpha is explicit data. Reviewed Stacks 07MB and 0FKV, and
   the full docstring argument. Independently searched leanfinder for Alexander
   Whitney compatibility with augmentation/restriction (eight generic tensor
   results), loogle for homologyMap/total (zero results), and rg in lean/.
   Existing cechCup_resolution_representatives requires a cover and quasicoherent
   coefficients and cannot prove this statement. CupCechTotalCochainPairing and
   CupCechTotalCochainAxes supply the cochain construction/axis calculations, but
   still require homology descent and identification with the characterized cup;
   the generic tensor_homology_pairing is for integer-indexed complexes, not the
   natural-indexed totals here. No exact duplicate or quick complete proof found.
   The beta obligation is strictly the second axis rather than the whole
   existential two-axis theorem. Verdict: pass; one genuine obligation remains.

4. Read the proof from the upper theorem downward: cup characterization, explicit
   transport, iso cancellation and alpha_class prove the alpha branch; beta alone
   uses the open imported theorem. The public imports provide signature objects,
   and the proof-only beta import is private. No shorter exact theorem was found.
   Read dag/units/sk-prop-av-cube.json: realized.statement and its step list are
   empty in this baseline, and this delivery does not alter or bypass that unit
   route or any realized node. No longer needed is complete relative to the
   absent baseline files. Verdict: pass.

5. Checked both nodes' statement, lean declaration/signature, proof steps,
   proof_deps union, source, chapter/unit and blueprint provenance. The total
   node follows the three proof steps actually written. The beta node records
   the remaining signed cochain and homology argument. New-node metadata and
   named sorry docstrings are present. Removed misleading old reviewed and
   reviewed_proof stamps, and recorded literal multiline Lean signatures.
   Verdict: pass.

Second reading changed only documentation and node metadata: explicit hole and
progress accounting, complete restoration signatures/users, and removal of stale
review stamps. The correct Lean proofs and signatures were left unchanged.
