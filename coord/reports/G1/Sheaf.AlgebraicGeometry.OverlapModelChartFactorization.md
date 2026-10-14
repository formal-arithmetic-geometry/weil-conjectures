## What changed

Proved `AlgebraicGeometry.overlap_model_chart_factorization` by reducing all routes to the same canonical pullback composite. Added private coherence helpers for pullback associativity, naturality, and tensor-to-abstract pullback compatibility. No public signatures or imports were changed.

## Proved and sorry left

The declaration `AlgebraicGeometry.overlap_model_chart_factorization` is fully proved. No `sorry` remains in the delivered module.

## No longer needed

None. Both stated proof dependencies remain used: `OverlapConjugateRestriction` supplies the chart comparisons, and `TensorPullbackCompositionIso` supplies the tensor compositor.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was accurate but omitted the explicit component-level pullback associativity and mate calculations needed by Lean. These were implemented as private proved helpers rather than new nodes.

## Second reading by G1

1. **Statements and interfaces.** Compared the delivered module with the repository version. The public imports and the complete signature of `AlgebraicGeometry.overlap_model_chart_factorization` are unchanged byte for byte; only its proof body and private helpers differ. Verdict: pass.

2. **Proof and axioms.** Compiled the module and all sandbox modules with `lcompile.py`; compilation succeeds with no warnings. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses canonical comparison isomorphisms, componentwise pullback pseudofunctor associativity, naturality, and cancellation. Verdict: pass.

3. **Split statements and searches.** No theorem was split off and no new node is added. The private helpers are proved, are not public API, and do not restate the target. Existing declarations in the imported modules supply the comparison and tensor-compositor facts. Verdict: pass.

4. **Shortest route and pruning.** The two stated public imports are both used. The proof directly invokes Mathlib's `Scheme.Modules.pseudofunctor_associativity`; the old DAG dependency on `lem-sc-left-adjoint-composition-iso-associativity` was unused and has been removed from `proof_deps`, with the proof route updated accordingly. Verdict: pass.

5. **DAG and unit agreement.** The target statement, source, chapter, and unit are unchanged. The node's proof and `proof_deps` now describe the actual route in the delivered Lean proof. The unit's realized route is unaffected. Verdict: pass.

Changed the DAG proof metadata to prune the unused associativity node and appended this second-reading record. No Lean source changes were needed.
