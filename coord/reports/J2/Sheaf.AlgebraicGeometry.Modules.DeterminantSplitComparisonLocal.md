## What changed

Proved `determinant_split_comparison_local` using the existing linear-map construction and local bijectivity lemmas, then converted the locally bijective maps with `LinearEquiv.ofBijective`. Proved `determinant_split_comparison_restriction` by rewriting with the supplied pointwise equality and applying naturality. No imports were added or removed.

## Proved and sorry left

Both declarations in `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal` are proved:
`determinant_split_comparison_local` and `determinant_split_comparison_restriction`. No `sorry` remains and no new holes were added.

## No longer needed

None. All existing imports are used by the module declarations or proof dependencies.

## Where the brief, the DAG or earlier work was wrong

Nothing found.

## Second reading by J2

1. **Interface and accidental changes.** Compared the delivered module with the repository
version. Both theorem signatures and all existing declaration statements are byte-for-byte
unchanged; the only change is replacing a proof-side `simpa` with `exact` in the local theorem.
Verdict: pass.

2. **Proof and axioms.** Compiled the module and the sandbox import set successfully. The file
contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; both declarations
have exactly the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. **Statements and split nodes.** The two split declarations are true reductions: the local
statement applies the existing linear-map construction and local bijectivity theorem, while the
restriction statement is direct substitution into the supplied naturality equation. Their node
statements match the Lean declarations and no duplicate library theorem was introduced. Verdict:
pass.

4. **Pruning and route.** The proof follows the recorded route through
`lem-sc-split-determinant-linear-maps` and `lem-sc-split-determinant-linear-bijective`; the
restriction proof is elementary. All imports remain needed by declarations or proof dependencies,
and no proof-dependency node can be removed. Verdict: pass.

5. **Unit and DAG agreement.** The local node's three proof steps and the restriction node's
elementary step agree with the Lean proof; the parent comparison route continues to use the
restriction node. The `sk-thm-picard-rr` unit route is preserved. Verdict: pass.

I changed only the local proof's final line from `simpa using ...` to the definitionally exact
`exact ...`; this is proof-only and does not alter the interface or imports.
