## What changed

Audited the repair-queue item
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore`.
The repository already has the repaired, proved descent-and-openness theorem.
Simplified the algebra descent proof of
`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`:
`algebraize` now acts directly on the two stalk maps and their composite,
instead of introducing three ring aliases, two homomorphism aliases, and
restating their flatness properties. Added a comment identifying the projection
as the base change of the flat test. The theorem signature, visibility,
docstrings, imports, and proof route stay identical. No consumer adaptation
or interface change is required.

The two DAG steps are retained: lift fibre points, descend through a faithfully
flat local stalk map using `Module.Flat.of_flat_of_faithfullyFlat`, then apply
`isOpen_setOf_finite_flat_stalks` and the restriction stalk criterion.
The unit `sk-prop-input-spreading` is unchanged. Existing node metadata already
records exactly these steps and dependencies, so no node update is needed.

## Proved and sorry left

The declaration
`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
(node `lem-sbc-stalk-normalization-depth-two-section-flat-core`) was already
proved in the starting repository. Its simplified proof compiles.
Starting textual holes: zero. Holes closed: zero. Holes added: zero.
No `sorry` remains in the delivered module and no new theorem or module is added.
This is a repair audit and proof simplification, not new proof progress.
The final delivery dry run checks the transitive axioms of its declaration.

## No longer needed

None. Both existing proof imports are required:
`Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus` supplies the finite
flat target locus, and
`WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` supplies the
already proved algebra flatness descent theorem. No node or module is pruned.
The Mathlib public imports used by the statement are preserved.

## Where the brief, the DAG or earlier work was wrong

The brief says this module still contains `sorry`; the current repository
contains none, and the original module compiles. The repair queue still refers
to the obsolete false normalization-only statement from upstream review #1428.
That statement was already corrected by the landed change record
`coord/changes/stalk-normalization-depth-two-section-flat-core.md`.
The current statement assumes `Flat (pullback.snd p t)` explicitly and proves
only descent and openness. It does not infer this assumption from depth two.
The normalization caller
`GaloisCover.stalk_normalization_depth_two_section_flat` explicitly assumes
`hZ`, the rational generic-section point, and passes it to
`GaloisCover.exists_stalk_normalization_split_formal_test` to obtain the test.
Thus the missing rational-point assumption has already been restored at the
normalization boundary, while the reusable core states the true general fact.
No target statement or definition is changed.

Checked degenerate cases: an empty fibre makes membership in the target flat
locus vacuous; an empty test cannot provide b; a non-surjective flat test is
sufficient because only the given point x must lie in its image. The proof
lifts every source point over x, so no global surjectivity is assumed.

Searches through Loogle, Lean Finder, and Mathlib grep found no shorter matching
ring-map flatness descent theorem. The existing source-library theorem is an
exact proved match and is retained. Compilation confirmed that the explicit
local-hom instance bridge is required after `algebraize`, and it is retained.

## Second reading by F2

1. Compared the complete delivered module with the repository using `diff -u`
   and checked the text before the theorem's `:= by` byte for byte. PASS:
   the only differences are two proof comments and the algebra descent block.
   The sole declaration's signature, visibility, documentation and imports are
   unchanged. No definition, target, node or change record is delivered.
2. Compiled the delivered file independently with `lcompile.py`: no errors or
   warnings. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`:
   exactly `propext`, `Classical.choice`, `Quot.sound`. PASS: no `sorry`, forbidden
   declaration or data chosen from an unproved existence statement occurs.
3. PASS: no statements were split off or added, so no new-node or restatement
   issue arises. Checked the empty-source and empty-fibre cases (the target
   locus condition is vacuous), and the test-point hypothesis excludes an empty
   test. Only the fibre over x is lifted; no global surjectivity is required.
4. Read the two imported proof results and searched the library for flat-test,
   faithful-flatness and descent formulations; repeated a Loogle search for
   `Module.Flat, Module.FaithfullyFlat`. PASS: Mathlib's tensor-product descent
   has a different premise; the source-library algebra descent used here is
   the direct proved match. The similar stalk-test proof in
   `SmoothLocalDepthTwoClosedFiberFlat` is private. Both proof imports are used;
   public imports provide statement vocabulary. No old proof dependency is
   omitted, so `No longer needed` is complete. The unit record is unchanged
   (its existing `realized` lists are empty); the delivery retains the same
   descent-and-openness subargument and bypasses no unit step.
5. Compared the node's Lean signature, two proof steps, `proof_deps` and
   `proof_origin` with the delivered proof. PASS: the algebra descent node and
   finite-flat-target-locus node are exactly its two non-Mathlib dependencies.
   The point lift, local faithfully flat stalk map, flat composite, restriction
   stalk isomorphism and stalk criterion occur as recorded. No metadata repair
   is needed.

Second reading changed only this report: added the independent checks and their
verdicts. The first worker's proof simplification is retained unchanged. There
are zero holes closed, zero holes added, and no pruned modules.
