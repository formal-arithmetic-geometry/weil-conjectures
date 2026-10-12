## What changed

The target theorem now combines two strictly smaller named intermediate theorems:
`isRegular_permutations_iff_subsequences` and
`isRegular_subsequences_iff_polynomial_variables`. Their proof bodies remain explicit,
named `sorry` obligations for follow-up workers. The target imports their modules.

## Proved and sorry left

The target `isRegular_permutations_subsequences_polynomial_iff` is proved by pairing the
two intermediate equivalences. Sorry remains in
`isRegular_permutations_iff_subsequences` and
`isRegular_subsequences_iff_polynomial_variables`, each with its own node.

## No longer needed

Removed the direct imports of `Sheaf.Paper.PolynomialIdealCoefficientsMonomial` and
`Sheaf.RingTheory.RegularSequenceSwapTwo` from the parent: they are dependencies of the
intermediate arguments, not of the pairing proof itself. The corresponding parent DAG
proof dependencies now consist of the two new nodes.

## Where the brief, the DAG or earlier work was wrong

The parent proof is substantially larger than a direct Lean proof available in the time
window. It was decomposed into the two mathematically independent equivalences rather
than leaving the parent theorem itself as a sorry.

## New nodes

`lem-weil-pbc-regular-sequence-permutations-subsequences-proof` records the induction
part proving permutation/subsequence equivalence.

`lem-weil-pbc-regular-sequence-subsequences-polynomial-proof` records the coefficientwise
polynomial argument proving subsequence/polynomial equivalence.

## Earlier second reading (a previous round; superseded)

The decomposition was checked against the unchanged parent statement. Each new theorem
has exactly one conjunct of the parent as its conclusion, and the target proof combines
them without weakening hypotheses or conclusions.

## Second reading by H1

1. **Visible statements.** Compared the delivered target module and its declarations with the repository version. The target theorem signature is byte-for-byte unchanged; the two intermediate modules are new declarations recorded by new DAG nodes.

2. **Proof validity.** Compiled all three modules with `lcompile.py --all`; compilation succeeds. The target proof contains no `sorry`, while the two explicitly split intermediate theorems retain exactly their named `sorry` obligations. No definitions contain `sorry`, and no forbidden axioms or unsafe declarations were added.

3. **Split statements.** Checked both intermediate equivalences against the parent theorem and the Stacks Project Tag 07DW argument. Each is a strict component of the parent, has the same hypotheses and conclusion as that component, and has its own node and source documentation. Mathlib searches recorded in the nodes found no existing theorem with either statement.

4. **Pruning and route.** The target proof only pairs the two intermediate equivalences, so the former direct imports and parent proof dependencies are unnecessary. The unit route remains represented by the two component nodes; no additional route bypass was introduced.

5. **DAG agreement.** Verified that the target node's proof and `proof_deps` name exactly the two intermediate declarations used by the Lean proof. The new nodes identify their modules, declarations, statements, sources, and split status consistently.

Changed only the target proof/imports, added the two documented intermediate modules and nodes, and recorded the decomposition above. No further repairs were needed.
