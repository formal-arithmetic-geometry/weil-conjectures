## What changed
Added a proof-only import of a fixed-degree helper and reduced the original universal theorem to that helper by introducing `n`, `j`, `m`, and `b`.

## Proved and sorry left
The universal declaration `singletonTensorDegreeComparison_pure_coface` is proved from the fixed-degree declaration. The new declaration `singletonTensorDegreeComparison_pure_coface_fixed` remains sorry and is recorded by node `new-etale-affine-singleton-tensor-pure-coface-fixed`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned geometric calculation could not be completed within this delivery; it was isolated as a fixed-degree intermediate theorem so it can be proved independently.

## New nodes
`new-etale-affine-singleton-tensor-pure-coface-fixed` records the fixed-degree intermediate theorem and its source calculation.

## Earlier second reading (a previous round; superseded)
The fixed-degree intermediate has the exact displayed interface and is the only remaining sorry; the universal theorem is a direct specialization.

## Second reading by N1

1. Compared the delivered item module with the repository version. The existing theorem signature is unchanged byte for byte; only its proof and a proof-only import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The universal theorem compiles, and the only remaining `sorry` is the named fixed-degree theorem, with no `axiom`, `unsafe`, or hollow definition. Verdict: pass subject to the documented split hole.
3. Read the fixed-degree statement and node. It is a true strict specialization of the universal pure-tensor equation, with the same hypotheses and one fixed `(n,j,m,b)`; its source and proof outline are recorded. Verdict: pass.
4. The proof uses the fixed-degree helper directly and retains the unit's coface route. The helper import is proof-only, and no existing dependency was removed. Verdict: pass.
5. Checked the node and report against the Lean declarations: declaration names, statements, proof dependency route, and remaining sorry agree. Verdict: pass.

I changed only this report by adding the required second-reading record; no Lean proof or statement was changed during review.
