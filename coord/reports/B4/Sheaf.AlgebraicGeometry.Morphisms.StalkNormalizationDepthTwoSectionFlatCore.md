## What changed

Reviewed the listed repair of
`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`.
The current repository already contains its generalized descent proof.
Preserved that proof and every signature and import. Restored the repository's
module and declaration documentation that the first sandbox version dropped,
including the rational generic-section hypothesis needed by the normalization
caller. Clarified only the two introductory proof comments.

## Proved and sorry left

`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
is proved (one of one declarations). No sorry remains and no split-off theorem
or hole is added. Relative to this checkout, holes closed: none; holes added:
none. This is a listed repair audit, not new net proof progress.
Local compilation succeeded; a scratch-copy `#print axioms` reports precisely
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. Both existing proof dependencies are used:
`lem-weil-pbc-flat-algebra-faithfully-flat-descent` and
`lem-sbc-finite-flat-target-locus`, through their existing plain imports.
The three public Mathlib imports supply the statement's scheme, Noetherian,
finite and flat notions. No module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The upstream review #1428 repair text refers to the obsolete normalization-only
statement. The current core instead explicitly assumes a flat test, its flat
pullback, and a point above x. Both current callers supply those assumptions.
The normalization caller passes hZ to its formal splitting theorem, then uses
the resulting split-test isomorphism to establish pullback flatness. The other
caller uses finite etale extension and punctured local purity. The repair does
not justify inferring flatness from depth two alone.
The first sandbox version accidentally removed this useful existing API
explanation; the second reader restored it.

## Second reading by B4

1. Compared the sole delivered module with the repository by diff. PASS:
   existing signature is byte for byte unchanged; no definitions, visibility,
   imports, or other modules changed. Existing docstrings were restored.
2. Compiled the module locally and compiled an axiom-probe scratch copy. PASS:
   no errors or warnings, no sorry, prohibited declaration, or hollow definition;
   only propext, Classical.choice, Quot.sound. The proof lifts each fibre point,
   uses flatness of the test projection and pullback composite, descends stalk
   flatness, and restricts to the open finite flat target locus.
3. PASS: no split-off statements or new nodes. In the empty-source case the
   fibre condition is vacuous and W is the entire target. For a nonempty fibre,
   the chosen test point lifts every source point; no global surjectivity of t
   is claimed or needed. No arbitrary data is chosen from an unproved theorem.
4. PASS: searched Mathlib's scheme Flat module for descent and faithful-flat
   results, and the Sheaf morphism modules for target-locus and core uses.
   No shorter applicable neighbourhood theorem was found. The proof already
   uses the existing algebra descent and finite-flat target-locus declarations.
   Both dependencies remain necessary. Read sk-prop-input-spreading.json:
   its realized entries are empty; preserved them and the formal-test route.
   Checked both current callers, including the normalization caller's hZ.
5. PASS: read the existing node's proof, proof_deps, proof_origin and verbatim
   Lean statement. They match the actual descent-and-openness proof and its
   documentation; no node edit is needed.

Second reading changed: restored existing module/declaration documentation and
clarified two proof comments. No proof body or statement repair was needed.
