## What changed

Simplified the proof of
`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction`
to two explicit rewrites by `hd`, followed by the naturality equation `hn`.
The delivery tool refreshed the checkout to a version already using `simpa only`;
the final proof uses explicit rewrites instead.
The statement, definitions, imports and local comparison construction are unchanged.
The existing DAG proof already describes exactly this substitution, so no node edit is needed.

## Proved and sorry left

The assigned module already contained no `sorry` when this session started.
Both `AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local`
(node `new-determinant-split-local`) and
`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction`
(node `new-determinant-split-restriction`) have complete proofs in the supplied checkout.
Holes closed: zero. Holes added: zero. Holes remaining in the assigned module: none.
This is a simplification of an already repaired proof, not new proof progress.
The local theorem retains its existing linear-map construction and local-bijectivity
proof dependencies; no claim is made that their transitive dependencies are sorry-free.

## No longer needed

None. No imports, nodes or modules were pruned. The local comparison still needs
`DeterminantSplitLinearMaps` and `DeterminantSplitLinearBijective`; the restriction
proof needs only its hypotheses.

## Where the brief, the DAG or earlier work was wrong

The brief says the assigned module contains `sorry`, but the supplied checkout has
none. Both nodes record an earlier proof landing. The module remains listed in
`coord/repairs.txt` for upstream review #1428, although the unconstrained tuple-family
statement has already been replaced by the natural-family hypotheses `hn` and `hd`.
The delivered proof checks that corrected interface directly. No statement repair,
new decomposition or downstream adaptation is necessary.

## Second reading by E3

1. **Interface and accidental changes.** Compared the delivered module with the repository version. The only change is the proof body of `determinant_split_comparison_restriction`; both theorem signatures, definitions, imports, and the local construction are unchanged byte-for-byte. Verdict: pass.

2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds with no errors and no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Axiom checks for both declarations report only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. **Statements and split nodes.** The local theorem and restriction theorem match their DAG node statements exactly. No new statements or holes were introduced, and the restriction proof is the direct substitution into `hn`. Verdict: pass.

4. **Pruning and route.** The imports are used by the declarations or their proof construction; the local theorem still follows the realized linear-map and local-bijectivity route. No proof dependency or module can be removed. Verdict: pass.

5. **DAG consistency.** The existing node proof descriptions agree with the explicit rewrites and application of `hn`; no node edits are needed. Verdict: pass.

Changed during second reading: appended this review only. No Lean source, DAG node, statement, import, or split-off theorem required repair.
