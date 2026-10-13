## What changed

Replaced the false whole-object conclusion of
`AlgebraicGeometry.clopenRankStrata_homology_presentation` by the concentrated
rank-stratum retract and its fixed-map property, retaining all original hypotheses.
Proved the repaired presentation in the item and rewrote
`AlgebraicGeometry.clopenRankStrata_homology_lift` from that retract; the lifting
signature and all target signatures are unchanged.

Added two fully proved modules:
`Sheaf.AlgebraicGeometry.ClopenRankStratumModuleProjector` constructs the scalar
natural idempotent explicitly, proves linearity, restriction compatibility and
support values by germ extensionality;
`Sheaf.AlgebraicGeometry.ClopenRankStratumDerivedProjector` splits the corresponding
chain idempotent using Mathlib, transports it through Q and proves its homology
identity and both support consequences. The private concentration helper in the
item uses Mathlib's existing t-structure/single theorem and writes the canonical
homology calculation by naturality. No arbitrary data definition is chosen from
an unproved existence theorem; the only new private data definition is the
explicit scalar multiplication transformation for supplied compatible sections.

All three modules compile together with no warnings through lcompile.py.
The delivery dry run is the final validation; nothing is pushed by this worker.

## Proved and sorry left

The baseline has one textual sorry, in
`AlgebraicGeometry.clopenRankStrata_homology_presentation`. Its old statement is
false and has NOT been proved. It is repaired, with the change record below,
and the corrected statement is completely proved. Thus the original-unchanged
hole proof count is 0 of 1; the repaired declaration has no sorry. This is a
statement correction, not a claimed proof of the old hole and not a decomposition.

The already sorry-free `AlgebraicGeometry.clopenRankStrata_homology_lift` now has
an actual proof from the corrected retract and Mathlib, without the false axiom.
New declarations `AlgebraicGeometry.clopenRankStratum_module_projector` and
`AlgebraicGeometry.clopenRankStratum_derived_projector` are completely proved.
All private helpers are completely proved. No sorry remains in any delivered
module. No holes are added or split off. Imported library dependencies may still
have their own existing holes; they are not claimed as closed by this delivery.
The ledger must distinguish the one repaired false hole from unchanged-statement
proof progress.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.DerivedCategory` (already available through its public
statement imports) and `Sheaf.AlgebraicGeometry.SchemeClopenIdempotent` (now used
in the module-projector module). The derived projector retains `Mathlib.CategoryTheory.Idempotents.Basic`: a
compile after removing it confirmed that it is needed for `idempotents_split`.
The closed-immersion, direct-image-algebra, locally-ranked and module-direct-image
public statement imports are retained.

Removed the earlier private `single_lift_of_homology_presentation` helper that
used a whole-object presentation. The claim that the complementary summand of K
is acyclic, and the claimed whole-object isomorphism, are not used anywhere.
The existing presentation node is repaired, not pruned. The scheme-clopen
idempotent node remains needed through the module projector; the concentrated
single Mathlib leaf remains needed through the concentration helper. No existing
node or library module is proved unnecessary in the targets' transitive closure.

For completeness, the repaired presentation no longer directly uses either old
proof dependency: `lem-weil-pbc-scheme-clopen-idempotent` is used transitively by
`lem-sc-clopen-rank-stratum-module-projector`, and
`lem-sf-derived-concentrated-single` moves to the lifting node's proof. Both remain
needed by the delivered proof; neither is globally pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old presentation concluded all of K is its degree-n
homology placed in degree n. The counterexample Z=Y=Spec(k), r=0, K=O_Z[0],
n=-1 satisfies its hypotheses and refutes that conclusion. The old DAG proof's
claim that the complementary summand has zero homology is the precise false step.
The original lifting theorem is true; only its supporting presentation is wrong.
The earlier sandbox removed this public declaration without a change record,
and left a new module-projector hole without a node or delivery report. This
attempt preserves the presentation's name, repairs its conclusion with all
hypotheses retained, proves both new projector declarations, and supplies the
node records and change record.

Edge cases checked: negative n uses the zero retract, negative m uses zero
prescribed homology, empty rank strata make the support identities vacuous or
zero, k≠q uses disjoint fibers, and a rank function with infinite image is allowed
because only one idempotent is constructed. No finite-image or quasi-coherence
hypothesis has been introduced. The unit's realized statement and step lists are
empty, so no fixed unit route is bypassed.

The referenced Stacks and blueprint source files are absent from this remote
clone. Read the official online [Tag 00EE](https://stacks.math.columbia.edu/tag/00EE)
and [Tag 08J5](https://stacks.math.columbia.edu/tag/08J5) and the existing node and
Lean proof texts. The sheaf/derived expansion is explicitly agent-written;
00EE supplies the idempotent correspondence, and 08J5 supplies truncation.
The existing Mathlib and library definitions and proofs were read locally.

## New nodes

`lem-sc-clopen-rank-stratum-module-projector`, module
`Sheaf.AlgebraicGeometry.ClopenRankStratumModuleProjector`: the scalar natural
idempotent for one stratum with its supported identity/zero values. Source:
Tag 00EE and the existing lifting proof's multiplication/support step. Fully
proved; no remaining item or sorry is split off.

`lem-sc-clopen-rank-stratum-derived-projector`, module
`Sheaf.AlgebraicGeometry.ClopenRankStratumDerivedProjector`: the derived retract
with vanishing and fixed-map clauses. Source: the chain-idempotent splitting
step of the lifting proof and the Mathlib idempotent-complete/derived-homology APIs.
Fully proved; no remaining item or sorry is split off. Both nodes record actual
LeanSearch (unavailable), Loogle, and grep searches, including prior attempt searches.

Changed existing node `lem-sc-clopen-rank-strata-homology-presentation` with its
statement correction, all old fields in the correction record, and its one citer.
Changed existing lifting node only in proof, proof_deps, and proof_origin.
Change record: `coord/changes/clopenRankStrata_homology_presentation.md`.

## Second reading by S4

1. **Interfaces — pass, declared correction checked.** Compared the item with
   the repository using `diff`; the existing lifting signature is byte for byte
   unchanged. The only changed public signature is the presentation named in
   `coord/changes/clopenRankStrata_homology_presentation.md`. Its hypotheses stay
   identical. Independently checked the counterexample with n=-1 and nonzero
   degree-zero homology: the old whole-object conclusion is false. The new retract
   statement proves the intermediate assertion actually needed. A repository-wide
   declaration search finds its sole caller in this item's lifting proof. No
   definition or target signature changes, and no other existing module is adapted.
2. **Proofs and axioms — pass.** Read all three modules, including the scalar
   transformation and generic chain-splitting helper, and compiled all three in
   import order through lcompile.py without warnings. Scratch copies with
   `#print axioms` for the presentation, lifting, module projector and derived
   projector show exactly propext, Classical.choice and Quot.sound, with no sorryAx.
   Scanned every delivered Lean file: no sorry, axiom, unsafe, opaque,
   implemented_by or extern. The scalar transformation is explicit data; the
   characteristic section is supplied by the proved unique-idempotent theorem.
   The chain representative, splitting, and concentration isomorphism are from
   proved Mathlib theorems. No data is selected from an unproved existence theorem.
3. **New statements — pass.** There are no split-off holes. The two new proved
   projector statements separate multiplication/support from chain splitting and
   homology transport; neither restates the lifting theorem. Checked empty fibers,
   disjoint fibers, negative n and m, and infinite rank image. Repeated searches
   with different wording using msearch Loogle and LeanFinder and rg over the
   library and relevant Mathlib sources. ModuleCat.smulNatTrans concerns a fixed
   ring and the forgetful functor, not module sheaves with varying restrictions;
   the Karoubi/cochain equivalence supplies splitting machinery, not these support
   and homology identities. The proof already uses Mathlib idempotents_split and
   the concentrated-single theorem. Found no shorter applicable exact result.
   Read the official Stacks [00EE](https://stacks.math.columbia.edu/tag/00EE) and
   [08J5](https://stacks.math.columbia.edu/tag/08J5); the sheaf/rank expansion is
   correctly identified as agent-written rather than a verbatim Stacks statement.
4. **Route and pruning — pass.** Read from the lifting conclusion through the
   corrected retract, derived projector and scalar projector. Naturality of the
   single/homology isomorphism checks the prescribed map, not just existence of
   some map. All public imports supply symbols in signatures; proof-only imports
   are plain imports. The old proof dependencies remain needed transitively or
   move to the lifting proof, now explicitly recorded above. No module is claimed
   globally pruned. Read dag/units/sk-thm-picard-duality.json: its realized statement
   list is empty and its step realization is [[]]; the unit record and its route
   are unchanged.
5. **DAG — pass after minor repair.** Checked each node's Lean statement verbatim
   against its declaration and proof_deps against the union of proof-step uses.
   The two new nodes include provenance, source, recorded searches, creation,
   blueprint, chapter, unit and Lean records. The existing lifting node retains
   its statement, and the presentation has its correction and sole-citer record.
   Removed the unused derived-category statement dependency from the module
   projector node, whose statement contains no derived objects.

Second reading changed no proof. Replaced the change record's flattened Old
signature with the repository signature verbatim, removed the obsolete
STATEMENT-DISPUTED marker from the now-proved repaired declaration, removed an
extra space before the module projector proof, removed its irrelevant statement
dependency, and made the old proof-dependency disposition explicit in the report.
The original false hole remains counted as 0 of 1 unchanged statements proved;
its repaired statement and both added projectors are proved, with no holes added.

The first dry run rejected an attempted stage-3 author label in statement_change.by:
the checker requires the literal form "<G> stage 2" for this field. Restored the
original "S4 stage 2" label to follow that schema; this correction was carried out
and reviewed during stage 3. No tool was changed or bypassed.
