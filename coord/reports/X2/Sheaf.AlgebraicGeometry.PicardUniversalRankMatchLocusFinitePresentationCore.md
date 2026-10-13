## What changed

Replaced the assigned theorem's sorry with a complete Lean fibre-product construction.
The theorem applies a single-direct-image rank representative first to E, then to its dual,
and proves both directions of the universal property using the two projections and
pullback.lift. Its signature and visibility are unchanged.

Added PicardUniversalSingleRankLocusFinitePresentation, stating the one-direct-image
construction without the structure-sheaf unit assumption, with local finite presentation.
Its full sourced proof plan includes homogeneous-rank fibres, mixed fibres, empty fibres,
perfect direct image, the universal degree-zero rank locus, and gluing.

Added PicardUniversalRankMatchSynchronization and proved
AlgebraicGeometry.Scheme.picardUniversalRankMatch_of_singleRankMatch_without_unit.
It restricts both witnesses to their intersection and compares reference ranks at a stalk.
If the inverse image is empty, its two ordinary direct images have rank zero, proved by
computing sections on an affine neighbourhood over the empty inverse-image open.
This lemma needs no structure-sheaf, finite-local-freeness, properness or flatness assumption.
Three private helpers are fully proved; none contains sorry.

Repair of the landing return: removed the duplicate private tensor_rank theorem.
The two restriction helpers now use the existing public ordinary-pullback fixed-rank
instance from WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank and the existing
SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso theorem, applied to a composite
isomorphism directly from ordinary pullback to the final restriction. There is no
intermediate tensor-pullback rank theorem or duplicate declaration. The suggested
PicardUniversalRankMatchConjunction.tensorRank is private and cannot be referenced by
its source name even with import all. No visibility or existing module was changed.

Only proof imports were replaced in the assigned module. Updated its node's proof,
proof_deps and proof_origin; created matching nodes for the two new public statements.
All three modules compile together via the prescribed lcompile.py --all command.

## Proved and sorry left

Closed the original hole:
- AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_finitePresentation_core
  (lem-sc-picard-universal-rank-match-locus-lfp-core).

Also proved the new auxiliary theorem:
- AlgebraicGeometry.Scheme.picardUniversalRankMatch_of_singleRankMatch_without_unit
  (lem-sc-picard-universal-rank-match-synchronization).

One new hole remains, in its own module:
- AlgebraicGeometry.Scheme.exists_picardUniversalSingleRankLocus_finitePresentation
  (lem-sc-picard-universal-single-rank-locus-lfp).

This is a decomposition: one original hole closed, one strictly smaller single-image
construction hole added, net zero holes. The assigned module has no sorry. The new single
condition tests only one direct image, with E fixing its reference rank; the assigned theorem
really combines two instances of it, proves the rank conjunction, and constructs their fibre
product. No arbitrary witness is used to define library data.

## No longer needed

Removed the assigned module's direct proof imports of:
- Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus
- Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange

These modules and their nodes lem-sc-perfect-h0-locally-closed and
lem-pc-rf-perfect-base-change remain needed by the new single-image construction, whose
proof plan imports them. They are relocated dependencies, not transitively pruned modules.
No module is claimed pruned from the targets' closure.

Removed the duplicate private helper AlgebraicGeometry.Scheme.tensor_rank; the two
restriction proofs reuse public rank APIs directly instead. No import was added in repair.

The existing PicardUniversalSingleRankLocus and PicardUniversalRankMatchConjunction,
with their structure-sheaf unit assumption, are not imported or used. Their nodes
lem-sc-picard-universal-single-rank-locus and lem-sc-picard-universal-rank-match-conjunction
are not needed by this construction. Neither was an original proof dependency, so this
is not a claim that they have disappeared from the targets' closure elsewhere.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly identified tensor_rank as a duplicate of the private
tensorRank in PicardUniversalRankMatchConjunction. It has been removed. Because that
existing helper is private, the restriction proofs instead use the existing public
pullback-rank instance and of_iso theorem directly; they do not restate the rejected fact.

The existing single-image and conjunction lemmas assume a universally invertible
structure-sheaf unit. This assumption cannot be supplied by the assigned theorem:
flat proper families can have empty or disconnected fibres. No existing declaration was
changed. The synchronization lemma proves that this extra assumption is unnecessary
for synchronization itself: empty inverse images force both ranks to be zero.

The original DAG marks the rank-decomposition step elementary and leaves gluing without
a named dependency. Those steps form part of the remaining sourced single-image
construction. Its docstring and node spell them out, including the neighbourhood of a
mixed-rank fibre and the empty-fibre component.

Mathlib searches were run through msearch.py (LeanFinder, Loogle, grep, and LeanSearch).
LeanSearch returned Internal Server Error and is recorded as unavailable. Source-library
and Sheaf searches found the related statements above but none with the required weaker
hypotheses and local finite presentation. Stacks Tags 0BDP, 0BDL and 0B91 were read directly.

Edge cases checked mathematically: empty test schemes are vacuous; empty fibres give
zero direct images and allow reference rank zero; rank zero on nonempty fibres uses the
same lowest-cohomology construction; mixed-rank fibres cannot acquire a constant reference
rank after extension of the residue field; F may differ in rank from E, since only its
direct-image rank is required to match E. No target, definition or existing signature changed.

The unit sk-prop-av-cube and its realized records are unchanged. The source route still uses
perfect direct image, universal lowest cohomology, and intersection of the two loci. The
blueprint ancestor script returns None for the parent because created.item contains module
names on the intermediate records; the new nodes explicitly refer to the theorem-of-cube
proof's application of Tag 0BDP and list the intermediate rank-locus nodes.

## New nodes

lem-sc-picard-universal-single-rank-locus-lfp:
lean/Sheaf/AlgebraicGeometry/PicardUniversalSingleRankLocusFinitePresentation.lean.
One direct-image rank representative, locally finitely presented, with homogeneous and
empty-fibre components replacing the connected-fibre hypothesis. This is the only new sorry.

lem-sc-picard-universal-rank-match-synchronization:
lean/Sheaf/AlgebraicGeometry/PicardUniversalRankMatchSynchronization.lean.
Fully proved local synchronization for arbitrary morphisms, with an explicit empty-preimage
rank-zero argument. Its proof uses the existing stalk-finrank and tensor-pullback statements
and proved source/Mathlib rank, restriction and pullback-carrier APIs.

No change record is required: existing statements, definitions and public imports are unchanged.

The second reading below predates this repair and must be renewed by the second reader.

## Earlier second reading (a previous round; superseded)

1. Compared the assigned module against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, proof text, and the node proof metadata changed.

2. Compiled all three delivered modules with the prescribed `lcompile.py --all` command. The assigned theorem and synchronization theorem have no `sorry`; the single-rank theorem retains exactly its named, documented split-off `sorry`. No forbidden declarations or hollow definitions were introduced.

3. Checked the new statements and nodes. The synchronization statement is strictly an auxiliary reduction and its proof handles both nonempty and empty inverse-image cases. The single-rank statement is strictly simpler than the assigned conjunction and has a matching node, source, proof plan, and Lean declaration.

4. Checked the proof route and pruning. The assigned proof uses the two single-rank loci, synchronizes their rank witnesses, and takes their fibre product; the unit route through perfect direct image and lowest-cohomology loci remains in the single-rank node. The removed direct imports are proof-only replacements and are recorded above.

5. Checked node and report consistency. The assigned node records the new proof dependencies and origin; both new nodes record their declarations and split/proved status. No target statement, definition, or public signature was changed.

Changed in this reading: added this review record only.

## Second reading by X2

1. PASS — Compared every delivered module with the repository. Only the assigned
   module already exists there. Its existing declaration, docstring, signature,
   visibility and public imports are byte-for-byte unchanged; its two proof imports
   and proof body changed. No existing definition or target changed, and no change
   record is needed. The existing node changes only proof, proof_deps and proof_origin.

2. PASS — Recompiled all three modules in import order with lcompile.py --all.
   Scratch-copy #print axioms checks show exactly propext, Classical.choice and
   Quot.sound for synchronization and all three private helpers. The assigned
   theorem and the single-image theorem additionally use sorryAx, as expected from
   the one documented split-off hole. There is exactly one delivered sorry, the
   named exists_picardUniversalSingleRankLocus_finitePresentation theorem; no axiom,
   unsafe, opaque, implemented_by, extern or hollow definition occurs. The assigned
   theorem is reduced, not independently proved without sorryAx.

3. PASS — Read both new declarations, their full proof docstrings and matching
   nodes. The single-image construction is a genuine smaller part of the argument:
   it constructs one direct-image rank locus, while the assigned proof applies it
   to E and its dual and proves the intersection construction. Independently checked
   empty schemes, empty fibres (ordinary pushforward zero), mixed reference ranks,
   rank zero on nonempty fibres, arbitrary F, and nonreduced further base changes.
   Read Stacks Tags 0BDP, 0BDL and 0B91 directly; the rank-component adaptation
   correctly excludes mixed fibres and includes the empty-fibre component. The
   remaining construction is substantial and cannot be closed in a few minutes.
   Fresh LeanFinder search for representability of universal zeroth cohomology,
   Loogle search for Module.rankAtStalk_eq_zero_of_subsingleton, and grep search for
   pushforward/rank combinations found generic gluing APIs and the rank-zero lemma
   already used, not an existing theorem of the new statements. Searched repository
   Picard modules and upstream cohomology/rank-locus modules. Existing single-rank
   charts and conjunction impose the unavailable universal structure-sheaf unit.

4. PASS — Followed the proof downward: two single-image representatives, proven
   synchronization, and the categorical fibre product. Restriction uses the public
   ordinary-pullback fixed-rank instance and of_iso directly, with no duplicate
   tensor-rank theorem. Each proof import is used; public imports serve signatures.
   No longer needed accounts for both original proof dependencies, which move to
   the single-image construction rather than leaving the target import closure.
   The unit sk-prop-av-cube and its realized record are untouched; its route through
   perfect direct image, lowest cohomology and intersection remains in the nodes.

5. PASS — Checked all three node records against the Lean declarations verbatim,
   and checked that proof_deps equals the union of the proof steps' uses. Both new
   nodes carry the required source, searches, creation, blueprint, chapter, unit
   and Lean records. The synchronization node describes the repaired restriction
   helpers and explicit empty-preimage rank-zero calculation; the assigned node
   records exactly the two new construction dependencies and predicates used.

Changed in this reading: renewed the independent review record after the duplicate
helper repair. No Lean or node repair was needed. Hole accounting remains one original
hole closed and one new hole added (decomposition, net zero); no modules pruned.
