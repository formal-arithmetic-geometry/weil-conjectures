## What changed

Kept the signature of
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_supported_ce_filtered_totals`
unchanged and replaced its entire sorry with a complete Lean reduction.

Added two proof-only imports and two new one-theorem modules:
`Sheaf.Paper.EtaleCESupportedFirstPageLifts` constructs coherent augmented lifts and
actual quotient-page realizations, with the degreewise filtration bounds for every
lower support bound of the input. It asserts no stationary comparison.
`Sheaf.Paper.EtaleCEStationaryComparisonsAtBounds` supplies stationary comparisons
and their naturality for arbitrary filtered sections-total maps satisfying the
representative equation. It uses explicit outer-step equalities and constructs no
inverse-image lifts or first-page identifications.

The combining proof derives antitonicity of the evaluated filtration from
`imageSubobject_comp_le`. For a witness a of support admissibility, it derives
`n+2 ≤ q+r` and `q-r+1 ≤ a` from the two components of the maximum bound.
Antitonicity gives precisely the outer bottom/top equalities. It then specializes
the generic stationary comparisons to the supported CE lifts, retains the strict
augmentation square and ht, and proves the required page equation for every hc.
No witness is extracted into a definition and no existing interface changes.

Updated the item's node proof and dependencies to match this reduction. The original
five steps are preserved as two construction/naturality subproblems and their
explicit integer-bound combination. No unit statement or realized proof step changes.

All three delivery modules compile individually in dependency order using lcompile.py.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_supported_ce_filtered_totals`
(node `lem-weil-pbc-supported-ce-filtered-totals`).

Added exactly two holes, each a whole public theorem proof in its own module:

- `AlgebraicGeometry.Etale.exists_etaleCE_supported_first_page_lifts`
  (node `lem-weil-pbc-ce-supported-first-page-lifts`).
- `AlgebraicGeometry.Etale.exists_etaleCE_stationary_comparisons_at_bounds`
  (node `lem-weil-pbc-ce-stationary-comparisons-at-bounds`).

This is a decomposition, not an axiom-free proof of the construction: one hole
closed, two added, net minus one. There are no sorries in the item's module or in
its private antitonicity helper. The two new docstrings and nodes describe the full
remaining arguments. Their statements omit different substantial parts of the
original theorem; neither is a renamed or hypothesis-repackaged copy of it.

## No longer needed

No imports or modules are pruned from the targets' closure. The existing public
EtaleCETotalSections import remains necessary for the unchanged statement.
The following old direct proof dependencies are no longer applied in the item's
combining proof; its two new nodes now supply the construction and naturality:

- `lem-sp-cartan-eilenberg-exists`.
- `thm-sp-if-e1`.
- `def-weil-pbc-termwise-hypercohomology-presentation`.
- `lem-sp-bounded-below-second-filtration`.
- `thm-sp-spectral-object-yields`.
- `lem-sp-filtered-complex-ZB-description`.
- `lem-sp-filtered-complex-associated-spectral-sequence-construction`.
- `lem-sp-filtered-complex-page-differential`.
- `lem-weil-pbc-cartesian-eilenberg-functorial`.
- `def-weil-pbc-inverse-image`.
- `lem-weil-pbc-ce-total-sections-comparison`.
- `lem-weil-pbc-sheafH-ext-derived-comparison`.
- `def-weil-pbc-cohomology-pullback`.
- `lem-sp-filtered-stable-subquotient-at-bounds`.
- `lem-sp-filtered-cohomology-image-finite`.
- `lem-sp-filtered-complex-quotient-image-comparison`.

These are retired direct proof edges, not claims that the underlying mathematical
results or modules are globally unnecessary. The construction and stationary
subproblem plans retain their lower theory; presentation, inverse-image,
cohomology-pullback and total-sections declarations still occur in the statement.

## Where the brief, the DAG or earlier work was wrong

The existing `exists_etaleCE_coherent_first_page_lifts` supplies no relationship
between its chosen filtration and *every* support bound of the original complex.
The existing `exists_etaleCE_stationary_page_comparisons` supplies only an
unspecified integer R. Neither theorem implies the explicit support-controlled
bound required here. They are useful construction patterns, but applying their
existence statements cannot recover the missing quantitative assertions. The two
new statements isolate exactly these differences without changing either existing
statement or making claims about arbitrary resolutions supported below a different
bound.

Edge cases checked in the subproblem statements: the all-zero input requires one
zero presentation valid for every a; negative total degrees and empty diagonals
still have top and bottom equal in a zero object; r=1 is allowed whenever the
explicit outer equalities hold; no strict inequality is incorrectly replaced by a
non-strict one (the upper bound is n+2); the generic stationary theorem assumes
both source and target outer equalities and representative compatibility. The
choice of support witness, outer-equality proofs and hc appears only in Prop and
is irrelevant. No universal naturality for unrelated page maps is asserted.

The locally published build initially lacked EtaleCEStationaryPageNaturality;
a subsequent cache refresh supplied it and the full reduction compiled. LeanSearch
returned an internal server error and Loogle was unavailable; LeanFinder and grep
were performed and found no exact theorem. The three search kinds are recorded.
The local literature checkout contains citation lists but not the referenced Stacks
source files; the cited official Stacks pages were read through the web tool. The
additional least-support and representative details are explicitly marked as agent
expansions in proof_origin.

## New nodes

`lem-weil-pbc-ce-supported-first-page-lifts`:
`dag/nodes/sec-curve-estimates/lem-weil-pbc-ce-supported-first-page-lifts.json`;
module `Sheaf.Paper.EtaleCESupportedFirstPageLifts`. It isolates steps 1--3 with
support bounds, leaving all stationary-page and abutment naturality work to the
other item. Its proof reconstructs the coherent data from supported resolutions;
it does not claim that an arbitrary witness of the existing existence theorem
has the support property.

`lem-weil-pbc-ce-stationary-comparisons-at-bounds`:
`dag/nodes/sec-curve-estimates/lem-weil-pbc-ce-stationary-comparisons-at-bounds.json`;
module `Sheaf.Paper.EtaleCEStationaryComparisonsAtBounds`. It isolates steps 4--5
under the actual bottom/top outer-step equalities, independently of input support
and the construction of augmented CE lifts.

No change record is required: no existing definition, signature or visibility
changed, and both new imports in the item's module are proof-only.

## Second reading by H1

1. PASS: compared the delivered item with the repository using diff and separately
   compared the entire existing theorem signature byte for byte. Only two plain
   proof imports, the private antitonicity theorem and the proof body were added.
   No existing definition, public signature, visibility or target changed. The
   existing node changes only proof, proof_deps and proof_origin. No change record
   is needed.
2. PASS as a decomposition: independently compiled all three delivery modules in
   import order through lcompile.py, without errors or warnings. A scratch copy
   with #print axioms reports exactly propext, Classical.choice, Quot.sound and
   sorryAx for the three public theorems; the private antitonicity helper uses
   only the three permitted axioms. The only delivery sorries are the two named
   new public theorem proofs already listed above. There are no definitions in
   the delivery, prohibited trust bypasses, or data definitions choosing arbitrary
   witnesses from unproved existence theorems.
3. PASS: read both complete new statements, docstrings and nodes, and the existing
   coherent-first-page and stationary-naturality statements. The construction
   isolates supported first-page lifts, while the second statement isolates
   quotient-to-image naturality under explicit outer equalities; neither restates
   the original conclusion. Checked zero inputs (all lower bounds simultaneously),
   a complex concentrated in a single integer degree (including negative degree),
   n below the support (zero diagonal), and r=1 when both outer equalities hold.
   For a nonzero input, the least nonzero degree exists because its support is a
   nonempty subset of the integers bounded below. After the shift, CE resolution
   and shift back, every original lower bound is respected. The stationary
   statement uses D.H_formula, both source and target bounds and the actual
   representative equation, so no arbitrary unrelated page map is admitted.
   Read the source formulas in Stacks Tag 012K (cycle/boundary formulas and graded
   cohomology equation) and Tags 015J/015K (CE construction and functoriality).
   Independent LeanFinder search for "associated graded homology image filtration
   canonical quotient naturality" found basic homology-projection naturality,
   not either complete assertion. Loogle with "Subobject, imageSubobject" returned
   unknown identifier, so it supplied no evidence. msearch grep and direct rg of
   lean/Sheaf found the existing stableSubquotient_at_bounds and
   boundedBelow_secondFiltration constructions; these do not provide the coherent
   supported family or the representative naturality conclusion. Neither new hole
   can be closed merely by applying the existing unspecified-bound theorem.
4. PASS after report repair: read the proof from its existential choices downward.
   The private helper proves evaluation antitonicity directly with the image lemma;
   the max-bound deductions give n+2 <= q+r and q-r+1 <= a. The applications of
   bot_unique and top_unique have the correct directions. The final stationary
   square uses exactly the chosen augmented lift and its sections-total map.
   Both new imports of the item are plain imports. Each new module's public
   stationary-naturality import is required for its signature's quotient-realization
   and representative types. No import can be removed from the delivered files.
   Expanded No longer needed to name all old direct proof edges replaced by the
   two subproblems, without claiming global module pruning. The unit sk-prop-h2
   and its realized fields are untouched; this lower-level refinement preserves
   the construction, first-page and stationary-comparison route.
5. PASS: the item's two proof_deps are exactly the new declarations applied in its
   body; the elementary bound argument and final specialization are recorded.
   Each new node has its source, full proof plan, proof_origin, searches, split
   status, creation/blueprint records, chapter/unit and matching Lean declaration
   and statement. The unresolved construction is explicitly reconstructed with
   supported resolutions rather than falsely derived from an arbitrary witness
   of the existing coherent existence theorem. The stationary plan retains the
   quotient-to-image representative argument needed for its naturality.

Second reading changed only this report: completed the retired-direct-dependency
list and added the independent review. Lean proofs and new statements required no
repair. One original hole closed, two lower holes added; net minus one, a
mathematically substantive decomposition, not a completed axiom-free construction.
