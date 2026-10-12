## What changed

Replaced the sole sorry in
Sheaf.AlgebraicGeometry.FiniteFreeResidueStalkHomotopy by a complete Lean proof from
minimal-complex existence. Added proof imports of
WeilConjectures.AlgebraicGeometry.Modules.FreeComplex and
Sheaf.AlgebraicGeometry.FiniteFreeStalkMinimalComplex. All existing signatures and
public imports are unchanged; no other existing module is adapted.

The new lemma separates the local unit-entry cancellation from the residue
cohomology argument. It takes a bounded finite free complex over the stalk,
without any cohomology hypothesis, and gives a minimal homotopy representative.
The main proof transports the residue homology across pullback composition and
homotopy equivalence, identifies reduced terms with homology using zero
differentials, recovers the free ranks, proves all terms off i vanish, and uses
the single-complex isomorphism and pullback compatibility to finish.

The two private helpers, free_zero_isZero and
nonempty_free_iso_of_pullback_rank, are proved. The latter works over any scheme
with a field-valued point and an already free module: it compares the residue
finrank with the original basis cardinality. It requires no unproved lifting
of an arbitrary residue isomorphism.

Both files compile through lcompile.py --all, without compiler or linter errors
or warnings. The source cancellation was checked against Stacks Tag 00MT,
lemma-add-trivial-complex, statement and proof.

## Proved and sorry left

Closed:
AlgebraicGeometry.Scheme.Modules.nonempty_stalk_homotopyEquiv_single_of_residue
(lem-pc-finite-free-residue-stalk-homotopy).
There are no sorries left in the item's module.

Added and left sorry:
AlgebraicGeometry.Scheme.Modules.exists_stalk_minimal_complex
(lem-pc-finite-free-stalk-minimal-complex), in
Sheaf.AlgebraicGeometry.FiniteFreeStalkMinimalComplex.
This is a decomposition: one original hole closed and one strictly separate
minimalization hole added, net zero. The residue-cohomology-to-single-complex
argument is fully proved; local cancellation and its affine sheaf comparison
remain. No data definition is chosen from this existential theorem; its witness
is used only inside the proof of the original proposition.

Edge cases checked: d = 0 needs no cancellation; rank sum zero gives the zero
complex; negative degrees vanish by strict support. For r = 0 the empty-generator
free sheaf is proved zero directly using freeHomEquiv. If i exceeds d, the minimal
representative has zero i-th term, and the residue rank hypothesis forces r = 0;
the Lean proof includes this case without requiring i to lie in the support.
An empty scheme has no y, so no excluded empty-spectrum case arises.

## No longer needed

None. No existing import was removed. The unit-entry-splitting node and module
remain necessary in the new minimalization lemma's proof plan; their dependency
is moved below that lemma, rather than pruned. No unit statement or realized
step is bypassed. No unused new proof import remains in the item's module.

## Where the brief, the DAG or earlier work was wrong

The original node's first and third steps provided no named declarations for the
affine conversion, termination of cancellation, or residue-rank identification.
The bare single-unit-entry splitting statement does not supply the complete
iterated sheaf-level homotopy equivalence. The new lemma isolates that gap.
Rank identification, including rank zero, needs no new sorry: existing proved
FreeComplex lemmas suffice, and the actual Lean combination is now written.

The checked-in literature payload is absent on this machine, so the cancellation
source was read at the official Stacks Tag 00MT page. Blueprint records and the
unit record sk-thm-picard-perfect were read locally. Blueprint searches for
minimal complex, minimal, and unit entry found no matching blueprint statement.
LeanFinder and Loogle found no minimalization theorem. LeanSearch returned an
Internal Server Error, recorded as unavailable; grep found only single-complex
and unrelated module lemmas.

The unit-entry splitting is an existing tool from sk-thm-p1, already used by the
original plan; this delivery introduces no alternative unit route.

## New nodes

lem-pc-finite-free-stalk-minimal-complex, in
 dag/nodes/sec-picard-framework/lem-pc-finite-free-stalk-minimal-complex.json,
is the bounded finite-free minimalization step, independent of any residue
cohomology condition, chosen degree i, or prescribed rank r. Its new module is
lean/Sheaf/AlgebraicGeometry/FiniteFreeStalkMinimalComplex.lean. It retains the
original unit-entry-splitting dependency and supplies complete source-based
proof instructions for the next worker. The original node's proof and
proof_deps now follow the delivered Lean argument. No change record is needed,
because no existing statement, definition, or public import was changed.

## Second reading by U1

1. Compared the delivered residue homotopy module with the repository version. Existing
declaration signatures and public imports are unchanged; only proof imports, private
helpers, and the proof body differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; there are no compiler errors,
warnings, forbidden declarations, or unlisted `sorry`s. The remaining sorry is exactly
`exists_stalk_minimal_complex`, with its named node and source docstring. Verdict: pass.
3. Checked the split-off minimalization statement against the stalk cancellation argument,
including zero-rank and empty-support cases. It is independent of residue cohomology and
strictly simpler than the target; no duplicate library theorem was found. Verdict: pass.
4. Read the proof top-down. It uses the minimal-complex dependency, pullback composition,
zero-differential homology, and existing finite-free rank lemmas; no shorter available
Mathlib or library route was found. Imports are minimal and no old proof dependency is
unused. Verdict: pass.
5. The DAG proof, proof dependencies, proof origin, and new-node Lean record match the
declarations and imports. The `sk-thm-picard-perfect` unit route remains realized through
the minimalization node and existing unit-entry splitting node. Verdict: pass.

Changed only the report by recording this review; no proof or statement changes were needed.
