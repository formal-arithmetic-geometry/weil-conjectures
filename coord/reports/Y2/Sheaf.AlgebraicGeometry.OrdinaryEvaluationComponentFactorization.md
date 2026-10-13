## What changed

Proved `AlgebraicGeometry.ordinaryEvaluation_component_factorization` in
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization`, with its original
statement and public imports unchanged. Added two proved private helpers:
`uncurry_projection` expresses an arbitrary uncurried dual projection as the projection
followed by evaluation, and `evaluation_factorization` moves the projection through
braiding and associativity and uses tensor-Hom naturality. The final theorem selects
the nonzero component branch and specializes this generic identity to the local site.
The proof follows the existing node's plan, so no node fields require changes.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.ordinaryEvaluation_component_factorization`
(node `lem-pc-ordinary-evaluation-component-factorization`).
Both private helpers are proved. No `sorry` remains in this module, and none was added
elsewhere. This is a proof, not a decomposition into new holed statements.
Single-file compilation passed without warnings (48.1 seconds).

## No longer needed

None. The sole public import `Sheaf.AlgebraicGeometry.OrdinaryEvaluationData` is needed
for the statement's definitions. The existing DAG dependencies supply those definitions,
the tensor-Hom equivalence and `moduleDualEvaluation`; no additional module is imported.
The finite-projective invertibility theorem itself is not used: only its module's
actual evaluation definition is needed. No node or module can be removed from this
module's import closure by this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The unit's `realized` lists do not contain
this node; the proof nevertheless follows its existing planned component calculation.
Direct scheme-local rewrites were cumbersome because elaboration expands local sheaf
categories. Generic private helpers avoid that issue while preserving all signatures.

## Second reading by Y2

1. Compared the entire delivered module with the repository version using `diff`.
   The existing theorem signature is byte-for-byte identical (also checked by a
   Python assertion); its docstring, visibility, options and sole public import
   are unchanged. Only two proved private helpers and the replacement proof were
   added. No definitions or other modules changed. Verdict: pass.
2. Compiled the delivered file through `lcompile.py`: clean, 46.4 seconds.
   Scanned for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by` and `extern`:
   none. A scratch copy with `#print axioms` for both private helpers and the
   public theorem compiled and showed exactly `propext`, `Classical.choice` and
   `Quot.sound` for each, with no `sorryAx`. Verdict: pass.
3. No statements were split off and no holes were added. Read both helper proofs:
   the first is tensor-input naturality plus the inverse laws of the equivalence;
   the second is output/input naturality and braiding/associator naturality.
   They hold for arbitrary maps, including zero maps and zero objects, and do not
   assume finite projectivity or bounded complexes. No data is selected from an
   unproved existence theorem by this delivery. Verdict: pass.
4. Searched the project with `rg` for evaluation naturality and tensor-Hom laws,
   and Mathlib through `msearch.py ... grep` for uncurrying naturality and evaluation.
   The existing tensor-Hom laws used here give the direct proof; generic monoidal
   uncurrying laws would require an extra comparison with the concrete equivalence.
   No shorter exact library theorem was found. The sole public import supplies
   statement definitions and cannot be removed. All three old proof dependencies
   remain needed: evaluation data, tensor-Hom structure, and `moduleDualEvaluation`
   from the finite-projective evaluation node (its invertibility result is unused).
   No node or import is pruned. Read `dag/units/sk-thm-picard-duality.json`: this
   component lemma is not a realized unit step; the existing route is preserved.
   Verdict: pass.
5. Read the item's node and all three dependency nodes. The existing node's proof
   describes exactly the implemented calculation, and its `proof_deps` records
   the definitions and naturality used. Its `proof_origin` correctly records C1's
   isolation of this argument. No new nodes or metadata corrections are needed.
   Verdict: pass.

Second reading changed only this report, adding the independent checks above.
The Lean proof was retained without alteration. One original hole closed, zero
holes added, zero split off; no remaining hole in the delivered module.
