## What changed

Replaced the sorry in `AlgebraicGeometry.limit_affine_transition_affine_comparison`
with a direct Mathlib proof. The limit point is affine by `Scheme.isAffine_of_isLimit`.
Global sections preserve the colimit of the opposite affine diagram, giving a ring
isomorphism with the chosen colimit. Its spectrum, composed with `c.pt.isoSpec`, is
the required isomorphism; coprojection compatibility and isoSpec naturality prove
each projection equation. No existing signature, definition, docstring or import changes.

## Proved and sorry left

Of the two originally open theorems, one is now proved without sorryAx:
`AlgebraicGeometry.limit_affine_transition_affine_comparison`.
The already proved `AlgebraicGeometry.exists_limit_affine_transition` remains compiled
and depends on the single remaining sorry:
`AlgebraicGeometry.exists_limit_affine_transition_core`
(node `lem-weil-pbc-limit-affine-transition-core`). Its existing docstring records the
relative-spectrum construction and local-to-global universal-property argument.
No new sorry or split-off statement is delivered.

## No longer needed

Removed the proposed new theorem and node `stage3-affine-comparison-data`, which merely
packaged the entire comparison conclusion together with affineness.
The comparison node no longer uses `lem-weil-pbc-spec-colimit-limit`; its proof_deps
is empty because its proof now uses Mathlib directly. That leaf remains needed by the
unproved core-existence node, so this does not claim global pruning of its module.
No import is removed: the one existing public import supplies the opensCone and
opensDiagram constructions in the public statement and the affine projection/open
limit theorems used by the unchanged outer proof.

## Where the brief, the DAG or earlier work was wrong

The first reader's proposed strengthened comparison was a restatement of the whole
open comparison, not a reduction to strictly smaller steps. Its new node lacked the
required search records and verbatim Lean statement, and its docstring lacked a full
natural-language proof. The module also produced a long-line warning. Removed this
proposal rather than delivering apparent progress. Mathlib already supplies all the
facts needed to prove the original comparison.

## Second reading by X2

1. Compared the complete module with the repository using diff. Every existing
   declaration signature is byte for byte unchanged; definitions, docstrings and
   imports are unchanged. No change record is needed.
2. Compiled the repaired file through lcompile.py with no errors or warnings. Scanned
   the complete source: only the named core-existence theorem retains sorry; no axiom,
   unsafe, opaque, implemented_by, extern or hollow definition occurs. Scratch-copy
   #print axioms checks show only propext, Classical.choice and Quot.sound for the
   comparison, with sorryAx additionally present for the core and the outer theorem.
3. Rejected and removed the new comparison-data theorem and node. Repeated Mathlib
   searches with leanfinder (affine limits and spectra of global-section colimits),
   loogle (IsColimit.coconePointUniqueUpToIso), and rg on Mathlib and lean/; inspected
   the actual declarations. No new statements remain to check. The proof works for
   a singleton diagram and for empty affine schemes/zero rings: neither nonzero rings
   nor nonempty underlying spaces are assumed. An empty indexing type is excluded
   by the original Nonempty hypothesis.
4. Used the shorter direct Mathlib route. The existing public import is needed by
   the signature and outer proof. Recorded the removed proposed node and the old
   comparison proof dependency above. Read dag/units/sk-thm-p1.json: none of its
   realized statement/step nodes is bypassed; this comparison is below the unit level.
5. Updated the existing comparison node's proof, proof_deps and proof_origin to match
   the Lean argument. The other two node proofs still match their unchanged code.
   There are no new nodes or change records.

Second reading changed: removed the restatement theorem/node, proved the original
comparison directly, corrected its node metadata, and replaced the inaccurate report.
