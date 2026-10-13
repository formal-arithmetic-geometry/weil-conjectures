## What changed

The signature and visibility of `affineOpenSections_inverse_image_compatible_refinement`
are unchanged. Its proof now obtains eventual agreement separately for each ordered pair,
uses `IsCofiltered.wideCospan` to synchronize the finitely many stages and their arrows to j,
and applies a proved pullback-cover construction at that common stage. The final equality
is proved using the square equations, the wide-cospan equations and presheaf functoriality.
The proof-only imports are `Sheaf.Paper.AffineOpenSectionsEventualCompatibility`,
`Sheaf.Paper.AffineOpenInverseImageRefinementData` and
`Mathlib.CategoryTheory.Filtered.Basic`.

The new covering theorem `affineOpenSections_refinement_data` is fully proved. It works
at any prescribed stage map and constructs its objects as actual categorical pullbacks.
It requires no sheaf, section, affine hypothesis, finite index set or limiting cone.
A mono with an explicit section proves the relevant base-change projections are
isomorphisms; pullback stability proves the stage cover, and factorization through inverse
isomorphisms proves the limit cover. No data definition chooses an arbitrary witness from
an unproved existence assertion.

The only unfinished part is eventual agreement for one pair of sections. This isolates
the equality-open and affine-limit-containment steps from finite synchronization and all
covering construction. Each new module has a source, a complete proof in words and its
own node; the parent node now follows the Lean assembly. The original unit route is kept.

Validation: all three sandbox modules compiled together with `lcompile.py --all`, with
no warnings or errors; the covering module also compiled individually. The finite
wide-cospan construction includes the empty index type without selecting an index.
The pairwise statement also allows empty overlaps, singleton diagrams and zero sheaves.
The delivery dry run checks the declaration signatures and axiom probes.

## Proved and sorry left

Closed original hole: `affineOpenSections_inverse_image_compatible_refinement`
(node `lem-weil-pbc-affine-open-inverse-image-compatible-refinement`). Its complete
Lean proof depends on the new pairwise statement below.

Added and fully proved: `affineOpenSections_refinement_data`
(node `lem-weil-pbc-affine-open-inverse-image-compatible-refinement-data`).

One added hole remains: `affineOpenSections_pair_eventual_agreement`
(node `lem-weil-pbc-affine-open-inverse-image-compatible-refinement-compatibility`),
in `Sheaf.Paper.AffineOpenSectionsEventualCompatibility`.
Its entire proof is `by sorry`; there are no other sorries in this delivery.

This is a decomposition, not a net hole reduction: one original hole closed, one
strictly smaller pairwise hole added (net zero). In contrast with the retained sandbox
attempt, the geometric covering step is proved and the remaining assertion is true.

## No longer needed

No original imports are removed. The parent no longer directly uses
`lem-weil-pbc-etale-section-zero-neighbourhood`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lem-weil-pbc-cartesian-square-pasting`,
`lem-weil-pbc-limit-image-contained-in-open`, or
`lem-weil-pbc-etale-base-change-continuous`. These remain dependencies of the pairwise
assertion or covering construction, so no original node or module is globally pruned.
`def-weil-pbc-category-colimit` remains a direct dependency for finite synchronization. The new covering module needs only the etale-site import;
the retained attempt's group-category and affine-morphism imports are omitted there.

The retained, unsubmitted `affineOpenSections_eventual_compatibility` declaration is
removed completely. Its arbitrary-stage compatibility assertion is not used. The two
retained new-node files are rewritten to describe the corrected pairwise step and the
proved covering construction; neither has the parent theorem as a dependency.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox proof was not a valid reduction. Its compatibility lemma asserted
that any refinement with the projection and covering equations already makes the
sections compatible, without choosing a sufficiently late stage. For example, take
X to be two disjoint affine points, a diagram with terminal target stage X and an earlier
stage consisting of just the first point, with limit that first point. Two sections of
the constant integer sheaf on the repeated identity cover of X can agree on the first
point and differ on the second. Their limit images agree, and the identity refinement
at X satisfies every covering-data equation, but the sections remain incompatible.
The false retained declaration has been deleted, rather than assumed or weakened in place.

The retained nodes also depended on their own parent theorem, giving a circular proof
plan, and their docstrings lacked complete proofs in words. These issues are repaired.
The retained report contained a purported second reading; it is removed so the actual
independent reader can write that section. The previous delivery-tool baseline failure
is no longer reproduced: the original module's hole is detected by the current tool.

## New nodes

`lem-weil-pbc-affine-open-inverse-image-compatible-refinement-compatibility` records
`affineOpenSections_pair_eventual_agreement`, the only new unfinished theorem. It
contains no finite-family or covering construction, and its proof plan uses the original
zero-neighbourhood, localization, pullback and limit-containment dependencies.

`lem-weil-pbc-affine-open-inverse-image-compatible-refinement-data` records the proved
`affineOpenSections_refinement_data`. It constructs covers at a fixed stage by actual
pullbacks and preserves the limit cover by base-change isomorphisms. There are no
changes to existing interfaces and no change records or forced adaptations.

## Second reading by E2

1. Compared the original module with the repository by diff and checked the existing
   theorem signature byte for byte: unchanged. The only changes to that module are
   three private imports and its proof. Both other modules are new; there are no
   interface changes, target edits, definitions or forced adaptations.
2. All three modules compile together in import order without warnings or errors.
   The only sorry is the complete named theorem
   `affineOpenSections_pair_eventual_agreement`. There is no forbidden declaration,
   hidden proof hole, or data chosen from an unproved existence theorem: the cover
   objects are categorical pullbacks. The delivery axiom probe checks all declarations;
   the parent legitimately retains sorryAx through the pairwise theorem. Explicit
   #print axioms probes returned propext, Classical.choice and Quot.sound for the
   cover lemma, and exactly those plus sorryAx for the parent and pairwise lemma.
3. Read Stacks Tags 09XM (the equality-open lemma) and 03Q6 (degree-zero continuity
   and descent of covers), and read the zero-neighbourhood and zero-detection modules.
   The pairwise statement is true: restrict the difference to the affine overlap,
   localize the inverse-image adjunction, and use its zero open and compact affine
   limit containment on the tail over j. Test arrows factor through the later overlap.
   The overlap is affine since both factors and their base D(j) are affine.
   Empty overlaps, empty limits, a singleton diagram and the zero sheaf introduce
   no nonemptiness requirement. This is strictly the pairwise equality step: it has
   neither finite synchronization nor a covering construction. The proved cover lemma
   also permits an empty index type and needs no limit or affine hypothesis.
   Repeated LeanFinder and grep searches with different terms (logged by msearch.py),
   and searched lean/Sheaf and lean/WeilConjectures. The candidates concern the structure
   sheaf or generic categorical limits, not this abelian etale sheaf assertion.
   No existing theorem closes the remaining geometric/localization argument in a
   few minutes. Both new modules have source and full proof docstrings and nodes.
4. Read the proof from the parent down: pairwise agreement, finite wideCospan,
   pullback cover, and functoriality. The synchronization explicitly equalizes the
   arrows to j and handles an empty B without choosing an element. The cover proof
   uses mono plus split epi and covering stability directly. Imports added only for
   proofs are private; the public imports supply the existing signatures. The old
   direct dependency nodes are now explicitly accounted for under No longer needed;
   they survive below the two new nodes, and no whole module is pruned.
   Read dag/units/sk-thm-p1.json realized: this auxiliary reduction changes none of
   the unit's statement or realized steps and follows the original local descent route.
5. Checked all three nodes against the Lean: proof steps match the finite assembly,
   pairwise geometric argument and proved pullback construction respectively;
   proof_deps is exactly the union of uses in each. New nodes have the required
   creation, source, search, blueprint and Lean records, with the parent's unit and
   chapter. Neither new proof depends on its parent. Normalized the three recorded
   Lean statements to the verbatim multiline signatures.

Second-reading changes: repaired the node statement formatting and expanded the
pruning report to list every old dependency removed from the parent's direct proof.
No Lean proof or statement needed repair. One original hole closed and one strictly
smaller hole added is a decomposition with net zero holes, not a complete proof.
