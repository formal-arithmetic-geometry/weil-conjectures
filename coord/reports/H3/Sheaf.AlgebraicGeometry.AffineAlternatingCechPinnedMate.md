## What changed

Reduced AlgebraicGeometry.affineAlternatingCech_pinned_mate without changing its statement.
The proof constructs e from the localized augmentation, inverse right-derived unit, and
section-model identification. It constructs t from inverse pullback of that identification,
ordinary termwise exchange, the target right-derived unit, inverse pulled-back augmentation,
and the single-complex identification. The private mate_factorization proves the required
categorical cancellations. The private pinnedBaseChange_naturality proves naturality directly
from the existing adjoint definition, using a natural transformation for its transpose.

Added AffineAlternatingCechExchangeResolution and DerivedBaseChangeUnitCompatibility, each
with one intermediate theorem. The latter also constructs moduleHomotopyBaseChange directly
from the existing moduleBaseChangeMap and the homotopy composition identifications. No data
is chosen from either new existence theorem in a definition. Resolution witnesses are
eliminated only inside the proof of the original theorem.

The second reader corrected the resolution proof to use affine pushforward base change
for the cartesian squares of the affine intersection inclusions, adding its proof import
and DAG dependency. It also replaced the unusable all-tuples resolution dependency
with the existing affine-open acyclicity theorem and upstream bounded-below unit
criterion and compatibility modules. The original module's public imports are unchanged.
Its four proof imports are replaced by
the exchange-resolution module. Updated the original node's proof, proof_deps and
proof_origin to follow the Lean proof. The unit's realized statements and steps are kept.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.affineAlternatingCech_pinned_mate
(lem-pc-affine-alternating-cech-pinned-mate). No sorry remains in the item's module.
Added two holes:

- AlgebraicGeometry.exists_affineAlternatingCech_exchange_resolution
  (lem-pc-affine-alternating-cech-exchange-resolution).
- AlgebraicGeometry.derivedBaseChange_unit_compatibility
  (lem-pc-derived-base-change-unit-compatibility).

This is a decomposition of one hole into two, not a complete proof free of sorry
in the target import closure. The intermediate statements separate geometric construction
and invertibility from the general derived mate/unit calculation. Neither is the original
existential conclusion under another name; the connecting proof explicitly constructs the
isomorphisms and combines the two statements. Both private helpers and all definitions are
proved. Validation is through lcompile.py and the deliver3.py dry run. The saved attempt's
second-reading section was removed because the recovery change needs a fresh second
reading. The first recovery dry run compiled the two intermediate modules in 41.0 and
23.8 seconds, but the pinned-mate module exceeded the 60-second limit. Normalizing
Scheme.Modules and Scheme.ringCatSheaf in the main proof made it compile without errors
or warnings in 59.2 seconds. This unfolds only category abbreviations inside the proof;
no definition or signature changes. The final dry run checks this exact three-module
reduction and its axiom probes. Nothing has been pushed.

## No longer needed

Removed the direct proof imports Sheaf.AlgebraicGeometry.CechResolution and
Sheaf.AlgebraicGeometry.ModulePullbackAffineSections from the item's module. The affine
sections module remains needed by the exchange-resolution theorem. CechResolution is
removed from that new module too: its all-tuples existential statement does not supply
the increasing-tuple unit calculation. Instead the plan uses
lem-pc-affine-open-pushforward-acyclic and the proved upstream bounded-below derived-unit
criterion and unit compatibility. Thus lem-pc-cech-resolution is no longer a proof
dependency of this reduction. A source import-closure comparison from TargetsCheck,
with the three sandbox modules overlaid, shows that the following modules and nodes
leave the targets' closure:

- Sheaf.AlgebraicGeometry.CechResolution (lem-pc-cech-resolution).
- Sheaf.AlgebraicGeometry.CechSheafResolution (lem-pc-cech-sheaf-resolution).

The latter prunes the existing hole AlgebraicGeometry.exists_cech_sheaf_resolution;
it does not prove that theorem. Only the two new intermediate modules enter the closure.
Also removed
the direct proof imports Sheaf.AlgebraicGeometry.DerivedPullbackComposition and
Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap, which remain transitively available
and are used by the naturality proof. The old direct proof dependency lem-weil-pbc-module-pullback-affine-sections
is now needed through the new resolution node.
def-pc-affine-alternating-cech-model is now only a statement dependency of the original
node and a proof dependency of the resolution node. None of these nodes is globally pruned.
No other original proof dependency is discarded: the model and fixed counits remain
in the statement, and the derived mate and composition definitions are used directly in the naturality proof.

## Where the brief, the DAG or earlier work was wrong

The first reader's resolution docstring cited open-square exchange for pulling back an
intersection pushforward. The recorded open-restriction theorem instead pulls back along
the bottom open immersion; it does not justify this square along arbitrary p. The
intersection inclusion is affine because X is separated over Spec A, so the existing
affinePushforward_baseChange theorem gives the needed comparison for its quasi-coherent
restricted module. The second reader corrected the docstring, node plan and proof import.

The existing cech_resolution_derived_direct_image describes all tuples. It does not identify
its complex with the increasing-tuple affineAlternatingCechModel. The original node already
acknowledges this distinction, and the new exchange-resolution statement leaves that
construction explicit instead of applying an incompatible all-tuples identification.

The finite affine Cech complex identity in Stacks Tag 02KH is used before taking cohomology;
its later flatness hypothesis is not used to assert tensor exactness here. The augmentation
remains a resolution after tensor pullback because it is locally contracted. Edge cases
checked in the new statements: r=0 forces X empty; zero G gives zero complexes; a one-member
affine cover gives the affine-section pullback comparison; g equal to the identity gives
identity ordinary exchange. The general unit compatibility has no affine, acyclicity,
quasi-coherence or flatness assumptions and also applies to zero or unbounded complexes.

Sources read: the blueprint lem-pc-rf-base-change-flat-module and the unit section from the
local literature mirror; Stacks Tags 02KH, 08HY and 09T5 online. The proofs of the new nodes
are marked agent-written expansions of the original node's Steps 1--3. Searches of both
Lean roots, DAG nodes and all blueprint nodes found no matching statements. Recorded
Mathlib searches used LeanFinder (classical derived functor comparison hits), Loogle
(no rightDerivedFunctorUnit hits), source grep (no matching Cech exchange lemma), and
LeanSearch (service returned Internal Server Error; recorded as unavailable).

## New nodes

lem-pc-affine-alternating-cech-exchange-resolution is in
lean/Sheaf/AlgebraicGeometry/AffineAlternatingCechExchangeResolution.lean. It supplies a
homotopy resolution with five invertibility properties and the explicit section-model
identification; it has no derived mate equation. It realizes the original Steps 1--2.

lem-pc-derived-base-change-unit-compatibility is in
lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeUnitCompatibility.lean. It compares the derived
mate and ordinary termwise exchange on the right-derived unit for any commutative square
and homotopy complex. It realizes the original Step 3 before transport through the
augmentation and section-model isomorphism. No change record or forced adaptation is needed.

## Second reading by H3

1. Interface: compared the entire original module with the repository using diff and
   the stage-3 declaration parser. The existing theorem signature and public imports
   are unchanged; statement_changed is empty. There is no changed existing definition,
   no forced adaptation and no change record needed. Both new theorem signatures match
   their node records verbatim. Verdict: pass.

2. Proof: compiled all three modules through lcompile.py without errors or warnings
   (14.2, 8.3 and 48.7 seconds before the documentation/import correction). Read
   mate_factorization: hg cancels the pulled-back q, hu cancels the source derived unit,
   hn transports the augmentation through the mate, and hp cancels the pulled-back
   augmentation. Read pinnedBaseChange_naturality: its sigma is a natural transformation
   and the pinned adjunction Hom equivalence gives exactly the square used by the target.
   Explicit #print axioms checks of the three exported theorems show only propext,
   Classical.choice, Quot.sound and sorryAx; moduleHomotopyBaseChange uses only the three
   permitted axioms. There are precisely the two reported named theorem holes, no hole
   in any definition, and no forbidden declaration. Resolution witnesses are eliminated
   inside a proposition proof; moduleHomotopyBaseChange is constructed directly from
   the ordinary natural transformation and composition isomorphisms. Verdict: valid
   decomposition, still dependent on the two open intermediate statements.

3. New statements: read both modules, their node plans, the recorded pinned adjunction
   compatibility in SchemeDerivedBaseChangeMap, the derived composition universal
   property, CechResolution and the explicit AffineAlternatingCechModel. Checked
   [Stacks 02KH](https://stacks.math.columbia.edu/tag/02KH),
   [08HY](https://stacks.math.columbia.edu/tag/08HY) and
   [09T5](https://stacks.math.columbia.edu/tag/09T5). The geometric statement concerns
   ordinary exchange on a locally split bounded resolution, so it needs no flatness.
   An empty cover forces X empty; zero G gives zero complexes; a singleton cover is
   the affine case. For the nonflat singleton example A=Z, X=Spec(Z/2), B=Z/2, the
   ordinary exchange and resolution units are invertible, while the left-derived
   counit can retain Tor; neither new statement asserts that counit invertible. The
   compatibility equation also specializes correctly to identity squares and zero
   complexes, and its proof uses no boundedness assumption. The two holes separate
   geometric construction from the general mate identity; neither restates the original
   existential isomorphism-and-equation conclusion. Independent searches: LeanFinder
   queries on Beck-Chevalley/derived-unit compatibility and finite strictly increasing
   locally split Cech resolutions, Loogle for derivedε_fac_app and
   mapHomotopyCategoryCompIso, and rg on both Lean roots for derived unit compatibility,
   alternating resolutions and homotopy exchange. Mathlib's derivedε_fac_app and
   derivedη_fac_app provide constituent adjunction identities, not this four-functor
   square; its localization adjunction results require functors already descending.
   No exact existing statement closes either hole in a few minutes. Found and reused
   affinePushforward_baseChange to repair the open-pushforward argument. Verdict: pass
   after that repair.

4. Route and pruning: the concrete e and t use exactly the invertibility clauses
   supplied by the resolution, then naturality and the general unit compatibility.
   Public imports in the new modules support their statements or the public ordinary
   exchange definition; construction-only dependencies are plain imports. The four
   removed direct proof imports and the old dependency nodes retained through
   the resolution/model or replaced by actual ingredients are listed above. The unused
   lem-pc-cech-resolution dependency is replaced by its actual acyclic-factor and
   derived-unit ingredients. Source import-closure comparison confirms that CechResolution
   and CechSheafResolution are globally pruned; the latter removes one existing hole.
   Inspected
   dag/units/sk-thm-picard-f-representable.json: its realized fields are unchanged
   (currently empty). The imported blueprint ancestor node preserves the finite affine
   Cech calculation and canonical-map identification; neither unit nor chapter route
   is bypassed. Verdict: pass. One hole is closed, two are added and one is pruned;
   this remains a decomposition. The pinned sorry ledger determines cumulative progress.

5. DAG: the original node changes only proof, proof_deps and proof_origin. Its new
   plan matches the explicit isomorphism assembly and generic cancellation proof.
   The two new nodes have their sources, complete prose proofs, statement dependencies,
   search records, creation metadata, blueprint ancestry, original chapter/unit and
   matching Lean records. Added the existing affine-pushforward-base-change dependency
   to the resolution node and explained the affine-morphism hypothesis. Replaced the
   all-tuples Cech dependency with lem-pc-affine-open-pushforward-acyclic and named the
   proved upstream derived-unit criterion and compatibility identity. Verdict: pass.

Changes by the second reader: corrected the open-pushforward proof citation and supplied
the affine-inclusion argument; added the ordinary affine-base-change proof import and
matching node dependency; replaced the unusable all-tuples Cech proof citation and
import with the affine-open acyclicity theorem and upstream bounded-below unit criterion
and compatibility; restored spacing at the original proof boundary; expanded the
pruning account, including the two modules actually leaving the target closure, and
wrote this independent review. No theorem statement was changed and
no additional hole was added. Final compile and all-declaration axiom validation are
performed by the deliver3.py dry run and delivery on these exact files.
