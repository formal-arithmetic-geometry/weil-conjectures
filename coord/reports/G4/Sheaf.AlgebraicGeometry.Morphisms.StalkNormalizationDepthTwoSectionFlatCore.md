## What changed

Repair audit of upstream review #1428, as listed in coord/repairs.txt.
The false statement cited by that review has already been repaired by E4:
coord/changes/stalk-normalization-depth-two-section-flat-core.md records the
landed interface change. The current core is the true flat-test descent theorem,
not the old assertion that depth two implies normalization flatness.

Updated the assigned module's documentation and proof comments to identify its
essential flat-pullback input and the exact location of the rational-point
hypothesis in the normalization application. Added the missing module blueprint
reference. Updated the assigned node's proof_origin to record this repair audit.
The Lean proof, both recorded steps, signatures, visibility and imports are kept.
No new theorem, definition, axiom or hypothesis is introduced.

Read Stacks Project Tag 0EYJ, especially its rational-point assumption and last
three paragraphs, at https://stacks.math.columbia.edu/tag/0EYJ. Read both direct
callers and the formal-test theorem. The normalization caller assumes
hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη and passes it to
GaloisCover.exists_stalk_normalization_split_formal_test. The returned isomorphism
to a coproduct proves Flat (pullback.snd n t), which is then passed to this core.
The other caller, flat_fibre_of_punctured_local_purity, proves test flatness via
an isomorphism with a finite etale extension; it needs no generic-section point.
Neither caller requires a forced adaptation, and no Challenge target changes.

## Proved and sorry left

Holes closed: none (0 of 0). Holes added: none. Holes split off: none.
AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core was
already proved at the baseline and remains fully proved. There are no sorries
in the delivered module, and no new nodes or declarations. This is a repair
audit/documentation delivery, not claimed as proof progress or decomposition.

The proof lifts each pair (z,b) to the pullback, proves faithful flatness of the
projection's local stalk map, uses the existing proved
Module.Flat.of_flat_of_faithfullyFlat, then uses
isOpen_setOf_finite_flat_stalks and restriction stalk isomorphisms to produce W.
The dry-run compiler and axiom probe validate the delivered module.

## No longer needed

None. No imports, nodes or modules were pruned. FiniteFlatTargetLocus and
WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic are both used.
The public Mathlib imports supply the statement's notions. The unit
sk-prop-input-spreading and its recorded route are preserved.

Search: Loogle Module.Flat, Module.FaithfullyFlat returned the tensor-product
flat-descent theorem, not the exact composable-algebra descent used here.
Read Mathlib AlgebraicGeometry/Morphisms/Flat.lean and searched its stalk and
descent APIs; rg of the source library located the exact existing algebra
lemma already used by the core. No replacement lemma or duplicate was needed.

## Where the brief, the DAG or earlier work was wrong

The repair entry reproduces a review of a superseded signature. The cone example
A = Q[x²,xy,y²] shows that depth two and a punctured etale cover alone do not
imply normalization flatness. It does not refute the present theorem, which
explicitly assumes a flat test whose pullback is flat. For such a test meeting
the cone vertex, stalkwise faithful-flat descent excludes a nonflat cone cover
from satisfying that hypothesis. The current normalization application includes
exactly the missing rational point through hZ; adding a new, unused generic-point
or dense-fibre binder to this abstract descent step would misidentify the repair.

The preceding sandbox report correctly found no proof holes but stopped without
making this repair scope reviewable. Replaced that stale report (including its
old second-reader section) with this audit; the new second reader writes their
own section. The module now explains why the rational-section data is needed
upstream and why it is not an additional assumption of flatness descent.

Edge cases checked: empty E gives a vacuous flat-stalk locus, empty T cannot
supply b, an empty fibre over x needs no stalk descent, and the trivial group or
zero-variable completion is covered by the formal-test theorem's split cover.
The point hb supplies intersection with the fibre; global surjectivity of t
is not assumed or used. All node statement and proof-dependency fields remain
unchanged, because the current statement was already the corrected one.

## Second reading by G4

1. PASS: Compared the sole delivered Lean module and sole node with the repository
   using diff. The existing declaration signature is byte for byte unchanged;
   no visibility, imports, definitions, executable proof terms or target changed.
   The Lean changes are documentation and two proof comments only.
2. PASS: Compiled the delivered file with lcompile.py (exit 0, no warnings).
   Rebuilt a scratch copy of the delivered file with #print axioms for
   AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core:
   only propext, Classical.choice and Quot.sound, with no sorryAx. Searched
   the delivered Lean sources for sorry and forbidden declarations: none.
   The pullback point is chosen only inside a proof, not as definition data.
3. PASS: No statements are split off or added. Checked the mathematical descent
   argument: base change makes the first projection flat; its local stalk map
   is faithfully flat; the flat composite descends through that map. Empty
   source/fibre cases are vacuous, and hb supplies the necessary test point
   without global surjectivity. Read the two callers and the split formal test;
   the normalization caller explicitly passes hZ before deriving test flatness.
   Verified the rational-point assumption and splitting argument against
   https://stacks.math.columbia.edu/tag/0EYJ.
4. PASS: Both proof-only imports supply explicitly used declarations. The public
   imports supply the signature's Noetherian, finite and flat notions. Repeated
   concept search with msearch.py grep for flat descent and read Mathlib's
   FlatDescent and LocalFlatDescent modules; their global fpqc APIs do not
   replace this pointwise test argument. The existing algebra descent theorem
   is already used. Nothing in the old proof_deps is unused; pruning is none.
   The unit sk-prop-input-spreading and its realized fields are unchanged
   (those fields currently contain empty arrays); the local-completion route
   in its final mathematical step is preserved, with no new realization claim.
5. PASS: Read both dependency nodes and their declarations. The node's two
   steps and proof_deps match the actual descent and open-locus proof. Its Lean
   statement matches the unchanged signature. No new nodes need review.

Second reading changed only the node's proof_origin.by back to E4: the proof
was written by E4 and is unchanged, whereas G4 performed this repair audit.
The audit remains recorded in proof_origin.note. No Lean repair was needed,
no holes were closed or added (0 of 0; 0 split off), and no modules were pruned.
