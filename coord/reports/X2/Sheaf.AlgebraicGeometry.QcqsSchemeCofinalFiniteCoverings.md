## What changed

Proved `AlgebraicGeometry.qcqs_scheme_cofinal_finite_affine_open_coverings` in
`Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings` without changing its signature.
Choose an affine neighbourhood within a selected cover member at every point, extract a finite
subcover, and index it by the subtype of the finite set of selected points. Mathlib proves
compactness of each affine open and of pairwise intersections in a quasi-separated space.
Updated the node's proof and proof dependencies to record this direct route.

## Proved and sorry left

Proved the module's sole sorry:
`AlgebraicGeometry.qcqs_scheme_cofinal_finite_affine_open_coverings`
(node `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`). No sorry remains or is added.
The file compiles cleanly through the prescribed local compiler. The construction also works
for an empty scheme and an empty cover index: the selected finite subtype can be empty.
The subtype is in Type u, so no resizing of the arbitrary Type v covering index is needed.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection` and dependency
`pqf-lem-qs-intersection-qc` from this node's proof dependencies. The declaration
`AlgebraicGeometry.compactSpace_inter_of_quasiSeparated` is unnecessary here because Mathlib's
`QuasiSeparatedSpace.inter_isCompact` applies directly. No other dependency is pruned.
This node is not a realized unit statement or step; no realized unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned project intersection lemma was unnecessary: the assumed
topological quasi-separatedness already provides exactly the required compact intersection.
No definitions, target statements, or public imports changed. No new nodes.

## Second reading by X2

1. **Visible changes and signatures.** Compared the delivered module with the repository version.
   The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof
   and its proof-only import were changed. Verdict: pass.
2. **Proof validity.** Compiled the module with `lcompile.py`; it compiles without errors and has
   no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof constructs a
   finite affine refinement using the affine-open basis and compact finite-subcover theorem, then
   uses `QuasiSeparatedSpace.inter_isCompact`. Verdict: pass.
3. **Statements and dependencies.** The sole node statement is unchanged and remains exactly the
   qcqs finite affine-cover refinement assertion. Its proof dependencies now match the declarations
   actually used; the old project intersection dependency is unnecessary, and no new statement or
   node was introduced. Verdict: pass.
4. **Pruning and shortest route.** Confirmed that the removed public import
   `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection` is unused and that Mathlib's direct
   quasi-separated intersection lemma is the shorter route. No realized unit statement or step is
   bypassed. Verdict: pass.
5. **Edge cases and metadata.** Checked empty scheme/cover behavior and arbitrary universe levels;
   the subtype index has the required universe and finite instance. The DAG proof text, origin, and
   dependencies have been synchronized with the Lean proof in all stage-3-owned fields. The
   pre-existing `tool_uses` field is protected metadata and is retained by the delivery tool.
   Verdict: pass.

The second reading changed only this report; the delivery tool retains the protected pre-existing
`tool_uses` metadata while delivering the corrected proof dependencies.
