## What changed

Replaced the proposed interval-form restatement with a complete proof of
`CategoryTheory.grothendieckBottomEdge_singleUnit`. The statement, definitions,
visibility and imports are unchanged. All supporting calculations are local proved
`have` statements inside the existing theorem: zero-shift normalization, the
single-object truncation factorization, the raw bottom-edge formula, and the
inverse source identification. Removed the proposed core theorem and its new node.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.grothendieckBottomEdge_singleUnit`
(node `lem-sc-grothendieck-bottom-edge-single-unit`). Proved 1 of 1 original holes.
No holes added, no split-off statements, and no `sorry` left in the delivered module.
The rejected proposal's `CategoryTheory.grothendieckBottomEdge_singleUnit_interval`
was removed rather than counted as a second hole closed.

Local compilation is clean (approximately 9 seconds). In a scratch copy,
`#print axioms CategoryTheory.grothendieckBottomEdge_singleUnit` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

None of the original imports, modules, or proof dependencies is pruned. Both public
imports are required to express the unchanged theorem statement. The proposed new
node `lem-sc-grothendieck-bottom-edge-single-unit-core` and its restatement theorem
are removed from this sandbox; neither is an old proof dependency.

## Where the brief, the DAG or earlier work was wrong

The first worker's interval theorem had the same hypotheses and conclusion as the
original theorem after unfolding `grothendieckBottomEdgeSourceIso`. It was a
restatement, not a strict intermediate truncation calculation; the original hole
was merely transferred to it. Its report incorrectly called this a proof. The new
node also attached its full docstring to the wrong declaration, and one comment
exceeded the line limit. The second reader replaced this proposal with an actual
proof using the existing DAG route and library lemmas.

## Second reading by F1

1. Compared the delivered module with the repository version using `diff`.
   Verdict: the existing theorem signature is byte for byte unchanged; no public
   declaration, definition, visibility or import changed. The only changes are its
   proof and theorem-local elaboration transparency options. No change record is
   required.
2. Compiled the final module locally through `lcompile.py` with no errors or
   warnings. Checked the source for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by` and `extern`: none. Independently compiled the scratch axiom
   probe: only the three permitted axioms occur. Verdict: complete kernel-checked
   proof. The local truncation lift comes from Mathlib's proved factorization;
   there is no data chosen from an unproved existence theorem.
3. Rejected and removed the proposed split-off statement because it restated the
   whole item. No new public statements or holes remain. The local heart argument
   is proved for every nonnegative derived object and every map from a single
   object, so zero objects and zero maps require no extra hypotheses. The main
   proof works uniformly for n = 0 and all n, with no left-exactness assumption on
   G. Searches through msearch (grep, Loogle, Lean Finder) and rg on the library
   found the existing truncation-factorization, heart-extensionality and
   homology-normalization building blocks, which the proof uses. Verdict: no
   duplicate or unproved auxiliary statement remains.
4. Reviewed the proof from the original conclusion downward. The bottom edge is
   explicitly expanded as homology of the inverse truncation projection followed
   by the inclusion. Zero shifts cancel, the existing degree-zero unit comparison
   identifies the source, and naturality for G reduces the result to the proved
   heart factorization. Both imports are required by the statement; every original
   proof dependency remains used. Read dag/units/sk-thm-curveestimate.json:
   realized.statement is thm-sc-proper-cohomology and realized.steps is empty.
   This helper is below the unit level and bypasses no realized unit or step.
   Verdict: route preserved; pruning list complete.
5. Read the original node's statement, three proof steps, proof_deps and
   proof_origin against the final Lean proof. They describe precisely the unit
   comparison, normalized truncation identity, zero-shift coherence and
   naturality used here, and need no change. Removed the proposed core node since
   its declaration no longer exists. Verdict: DAG agrees with Lean.

Changed by the second reader: removed the restatement theorem and node, proved the
original theorem in full, repaired the long line, and corrected this report.
