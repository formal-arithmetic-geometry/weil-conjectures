## What changed
Proved `AlgebraicGeometry.IsCurve.exists_sepClosed_comparison_core` directly, following the existing node's two-step plan. Recover the field homomorphism using `Spec.preimage`, choose `K' = AlgebraicClosure k'`, and let `K = algebraicClosure k K'`. Mathlib supplies algebraic closedness and pure inseparability over the separably closed ground fields. Construct both schemes as pullbacks. Paste the second pullback with the original square, cancel the first pullback using `IsPullback.of_right'`, and obtain the projection equality from `IsPullback.lift_fst`.

Added proof-only imports `Mathlib.FieldTheory.AlgebraicClosure`, `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, and `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`. Existing signatures, docstrings, and public imports are unchanged. The proof retains the node and unit route; no new nodes or intermediate statements are needed.

## Proved and sorry left
Proved `AlgebraicGeometry.IsCurve.exists_sepClosed_comparison_core`, the module's only sorry. No sorry remains in the delivery. Local compilation succeeds without warnings; the delivery dry run also checks the declaration's axioms and compiles on the server.

## No longer needed
None. No existing import, proof dependency, node, or module is pruned. All eight planned dependency nodes supply the field closure, spectrum, universal-homeomorphism, or pullback ingredients used in the proof. No modules from the larger sheaf plan are needed beyond these already available ingredients.

## Where the brief, the DAG or earlier work was wrong
No mathematical or interface correction was required. Several proof dependency nodes have no `lean` record but do have exact `mathlib_match` records; those Mathlib declarations suffice. The construction works without using the curve or properness assumptions, preserving their presence in the existing statement. It needs no nonemptiness assumption and covers empty and zero-dimensional schemes. Exploratory intermediate declarations were removed before delivery.

## Second reading by F1

1. **Visible changes:** Compared the delivered module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only proof-only imports
   and the theorem proof differ. No change record is required.
2. **Compilation and axioms:** Compiled the module with `lcompile.py`; it succeeds with no
   warnings or errors and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The proof uses standard algebraic-closure and pullback results, with only
   the permitted classical axioms.
3. **Statements:** No statements were split off or added. The theorem remains exactly the node
   statement, including its edge cases.
4. **Pruning and route:** The proof follows the node's compatible algebraic-closure and
   pullback-pasting route. All proof-only imports are used, and no old proof dependency or unit
   route is discarded.
5. **DAG agreement:** The node's `proof`, `proof_deps`, and `proof_origin` agree with the
   implementation: algebraic closures supply field data, spectrum maps give the
   universal-homeomorphism projections, and pullback pasting supplies `a` and the projection
   identity. The unit's realized route is preserved.

No repair was needed after this second reading; this review record is the only additional change.
