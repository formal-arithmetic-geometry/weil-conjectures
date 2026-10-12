## What changed

Repaired `Sheaf.Algebra.Homology.ZigzagBoundaryReduction` after the landing
checker rejected two duplicate private helper statements. Removed
`HomologicalComplex₂.row_projection_exact` and
`HomologicalComplex₂.zigzagIndex_eq_iff` entirely. Imported
`Sheaf.Algebra.Homology.ZigzagToRowCokernel` privately and extracted the first
clause of its existing public `HomologicalComplex₂.exists_zigzagToRowCokernel`
theorem for projection surjectivity and kernel-image equality. Proved the only remaining index disequality directly by applying `congrArg`
to the first coordinate: equality would imply `1 = 0`.

The existing signature, visibility, hypotheses, conclusion and docstring of
`HomologicalComplex₂.zigzag_boundary_reduction` are unchanged. The explicit
boundary tuple and residual-cycle proof are retained. Updated the sandbox
node `new-zigzag-boundary-reduction` to record the reused theorem dependency.

## Proved and sorry left

Closed one hole: `HomologicalComplex₂.zigzag_boundary_reduction`
(node `new-zigzag-boundary-reduction`). No sorry remains in the delivered module.
Added zero holes; split off zero statements. No new helper declarations remain.

The proof still uses the existing `HomologicalComplex₂.zigzagModule_functorial`
from `Sheaf.Algebra.Homology.ZigzagModuleFunctorial`, which has its own existing
sorry. This is a proof from the named dependencies, rather than a claim of a
sorry-free transitive axiom closure. The reused row-cokernel theorem is already
proved in its own library module.

## No longer needed

Removed the added proof-only import
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`: its exactness API is no
longer used directly. Removed both duplicate private helpers named above.
No existing DAG nodes or project modules are pruned; all original dependencies
remain used, and the row-cokernel-map node is now an additional proof dependency.
The existing public imports are retained for the unchanged interface.
`dag/units/sk-thm-p1.json` is unchanged; this node is not a unit realization,
and the existing two-step boundary-reduction argument is preserved.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private `row_projection_exact` and
`zigzagIndex_eq_iff` statements in `ZigzagToRowCokernel`. Although those private
helpers cannot be called across modules, its public theorem exposes the needed
projection exactness clause. The earlier second reading incorrectly concluded
that importing this theorem could not shorten the proof. This repair removes
both duplicates and reuses that clause, while using first-coordinate congruence directly.
No mathematical statement or definition was changed; no forced adaptations or
change records are required. The previous second reading concerned the returned
version and is omitted pending a fresh independent reading of this repair.

## Second reading by A2

1. Compared the delivered module with the repository version. The theorem signature,
   hypotheses, conclusion, visibility, and docstring are byte-for-byte unchanged; only
   the proof and one private proof import differ. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`; it has no local `sorry`, `axiom`,
   `unsafe`, or forbidden implementation declarations. The remaining `sorryAx` in
   `#print axioms` comes only from an imported upstream theorem. Verdict: pass.
3. Checked the proof route and searched the library for duplicate declarations. The
   proof reuses `exists_zigzagToRowCokernel`; the two former duplicate private helpers
   are removed, and the direct congruence argument is valid for both `n = 0` and
   `n + 1`. Verdict: pass.
4. Checked pruning and dependencies. The added row-cokernel import is proof-only,
   the removed exactness import is not needed by the proof, and the unit route and
   realized fields are unchanged. Verdict: pass.
5. Checked the node against the Lean proof. The node records the reused row-cokernel
   theorem in `proof_deps` and the repair in `proof_origin`; no statements or new
   split-off nodes were added. Verdict: pass.

Changed during this reading: no further Lean or DAG changes; added this independent
review record only.
