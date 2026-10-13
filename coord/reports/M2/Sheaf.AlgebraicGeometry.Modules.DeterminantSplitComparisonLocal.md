## What changed

The sandbox copy compiles both declarations. The local proof of
`determinant_split_comparison_local` uses `simpa using hd ...` at the final
formula step; this is definitionally the same completed proof as the current
library proof. `determinant_split_comparison_restriction` is unchanged.

## Proved and sorry left

`determinant_split_comparison_local` and
`determinant_split_comparison_restriction` contain no `sorry`. No new holes were
added; the assigned item was already proved in the checkout before this
sandbox delivery.

## No longer needed

None. All existing imports remain needed by the declarations or their types.

## Where the brief, the DAG or earlier work was wrong

The item was assigned although both declarations were already complete in the
current checkout. This delivery only verifies the existing proof route.

## Second reading by M2

1. **Statements and accidental changes.** Compared the delivered module with the repository copy. Both theorem signatures and definitions are byte-for-byte unchanged; the only difference is the proof term in `determinant_split_comparison_local` (`simpa using` in place of `exact`). Verdict: pass.
2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it succeeds without warnings or `sorry`. Checked both declarations with `#print axioms`; dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Split-off statements.** No new statements or nodes are introduced. The two existing declarations are proved directly, and no duplicate Mathlib or upstream result is claimed. Verdict: pass.
4. **Shortest route and pruning.** The local proof follows the node route: construct the natural linear maps, obtain local bijectivity, and convert each map with `LinearEquiv.ofBijective`; the restriction theorem is direct substitution. All imports remain used by declarations or their types, and no proof dependency can be removed. Verdict: pass.
5. **DAG and unit agreement.** The node proof and proof dependencies match the two imported determinant lemmas and the elementary conversion step; the unit route through local construction and bijectivity is preserved. Verdict: pass.

Changed only the final proof elaboration from `exact` to `simpa using`, which is definitionally equivalent and compiles cleanly. No holes were closed or added beyond the already complete declarations; no modules or imports were pruned.
