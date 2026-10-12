## What changed

Restored the assigned module and its unchanged signature from the repository. Proved
`Algebra.exists_gabber_relation_after_base_change` by applying the base-changed quotient
map to the upstairs tensor coefficient relation. The proof constructs a tuple supported
at each index to show the coefficient map lands in the range of L, then uses tensor
functoriality and linearity to kill the finite sum.

Added `Sheaf.RingTheory.FiniteGabberUpstairsRelation` with one public intermediate
statement, `Algebra.exists_gabber_upstairs_tensor_relation`. Updated the assigned node
and added a node for the remaining upstairs construction. This is a decomposition.

## Proved and sorry left

Closed: `Algebra.exists_gabber_relation_after_base_change` (one of one original holes).
Added: `Algebra.exists_gabber_upstairs_tensor_relation`, left sorry in the new module,
node `lem-weil-pbc-gabber-upstairs-tensor-coefficients` (one hole).
The relation holds in C tensor B, with coefficients in C tensor I, before taking the
quotient. The quotient calculation is fully proved in the assigned module.

## No longer needed

No mathematical dependencies are pruned. The direct proof import
`Sheaf.RingTheory.LiftIdempotentUpstairs` is replaced by
`Sheaf.RingTheory.FiniteGabberUpstairsRelation`; idempotent lifting remains needed
inside that new node's proof plan. The original nine proof dependencies are retained
in the new node where applicable, rather than being advertised as eliminated.

## Where the brief, the DAG or earlier work was wrong

The saved attempt had put an unrelated multivariate-polynomial localization theorem
in the assigned module. This removed the assigned declaration and caused deliver3.py
to crash with KeyError during its declaration comparison. Restoring the correct module
repairs this input problem without modifying the delivery tool.

The saved coefficient theorem asserted a relation already in B, while the cited
construction first gives a relation after base change. Its saved node and two unproved
declarations were removed and replaced by the single tensor coefficient statement.

Read the source proof at `/home/ubuntu/c1-stacks-review/more-algebra.tex`, lines 2290ff,
a local copy of the document recorded in the DAG. Edge cases checked: multiplying the
second-factor monic annihilator by X ensures d >= 1 even when that factor is the zero
ring. If I is zero the coefficients vanish and idempotence gives the relation; if A is
the zero ring all tensor terms vanish. No nontrivial-ring assumption is added. Coefficients
are tensors, so the statement requires no finite generation of I. Existential witnesses
are eliminated only inside a theorem proof; no data definition selects arbitrary witnesses.

## New nodes

`lem-weil-pbc-gabber-upstairs-tensor-coefficients`: steps 1-8 of the original plan,
followed by representing the extended-ideal coefficients as tensors in C tensor I.
The source, complete proof in words, unchanged hypotheses, positive degree, and exact
Lean signature are recorded. No interface change or forced adaptation is made.

## Second reading by R2

1. **Signatures.** Compared the assigned module with the repository version. Existing theorem statements are byte-for-byte unchanged; only the proof and proof-only import differ.
2. **Proof.** Compiled both delivered modules with `lcompile.py --all`; both compile cleanly. The assigned theorem has no `sorry`, axiom, unsafe, opaque, extern, implemented_by, or hollow definition. The sole remaining `sorry` is the named upstairs theorem and has its node.
3. **Statements.** The quotient proof applies the quotient map to the upstairs tensor equality and proves each coefficient map lands in `range L`; the split statement is strictly simpler and preserves all hypotheses, positive degree, and tensor coefficients, including zero-ring cases.
4. **Pruning and route.** The assigned proof uses the upstairs relation and quotient/tensor APIs only. The old direct `LiftIdempotentUpstairs` import is removed from this module; its construction dependencies remain behind the split node. The unit route is retained.
5. **DAG and search.** The assigned node's proof and dependencies match Lean, and the new node records its source, exact signature, proof origin, and searches. No duplicate declaration was found.

Changed during second reading: restored the correct assigned module, added the upstairs split module and node, updated the assigned node's proof route, and added this review record.
