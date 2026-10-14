## What changed

Marked `AlgebraicGeometry.affineDerivedPushforwardSheafEdge_compatibility` as
`STATEMENT-DISPUTED`; no proof change was made. The theorem quantifies over an
arbitrary natural transformation `ε` while asserting that it equals the canonical
right-derived-unit comparison.

## Proved and sorry left

The existing sorry in `affineDerivedPushforwardSheafEdge_compatibility` remains,
with node `lem-pc-affine-derived-pushforward-sheaf-edge-compatibility`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The statement is false as written: `ε` has no hypothesis characterizing it as the
affine edge. Replacing any candidate edge by the zero natural transformation leaves
the hypotheses unchanged but generally changes the left-hand side, while the
right-hand side is fixed by the derived-functor unit. The node should quantify over
the canonically constructed edge (or add an axiom characterizing `ε`) rather than
all natural transformations.

## Second reading by F3

1. Compared the delivered module with the repository version. The theorem signature,
imports, and declaration body are byte-for-byte unchanged; only the explanatory
`STATEMENT-DISPUTED` docstring marker was added. No definition, target statement, or
other module was changed. Verdict: no accidental interface change.

2. Compiled the module with `lcompile.py`; it succeeds. The remaining `sorry` is
exactly the named theorem `AlgebraicGeometry.affineDerivedPushforwardSheafEdge_compatibility`,
which is listed above. There are no forbidden declarations, hollow definitions, or
new unnamed holes. Since the theorem is disputed, no proof claim is made. Verdict:
compile and hole accounting are consistent.

3. Checked the statement against its edge case. The quantified natural transformation
`ε` has no condition tying it to the canonical affine edge. Replacing a candidate
edge by the zero natural transformation preserves all hypotheses but changes the
left side in any nonzero case, while the right side is fixed. Thus the statement is
false as written and the disputed marker is warranted. No new statement was added.
Verdict: the counterexample is mathematically decisive.

4. Checked the proof route and imports. There is no proof route to a false universal
statement, so no imports can be pruned and no unit route is bypassed. The existing
module retains its original public imports and the node retains its recorded proof
dependency. Verdict: no pruning change is justified.

5. Compared the DAG node with the Lean declaration. The node records the same
quantification over `ε`, the same conclusion, source references, and split status;
the Lean declaration matches it exactly. No new node or change record is needed.
Verdict: DAG and Lean agree, with the item correctly left open pending statement
correction.

Changed only this report and the disputed explanatory docstring already present in
the delivered module; no holes were closed and none were added.
