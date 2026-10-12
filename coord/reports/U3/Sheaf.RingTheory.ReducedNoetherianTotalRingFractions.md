## What changed
Split `fractionRing_pi_bijective_of_compatible` into injectivity and surjectivity halves. The original theorem and the downstream total-fractions theorem now compile using these named intermediate statements.

## Proved and sorry left
The original bijectivity theorem is proved from `fractionRing_pi_injective_of_compatible` and `fractionRing_pi_surjective_of_compatible`. The two strictly smaller intermediate theorems retain `sorry` proofs and are recorded as new DAG nodes.

## No longer needed
None; all existing imports remain required by the total-fractions construction.

## Where the brief, the DAG or earlier work was wrong
The full finite-product argument is not available as a single Mathlib theorem, so the original hole was decomposed into its injectivity and surjectivity components.

## New nodes
`lem-weil-pbc-fraction-ring-pi-injective` and `lem-weil-pbc-fraction-ring-pi-surjective`, both in the sandbox DAG and both stated in the item module.

## Second reading by U3

1. PASS: compared the delivered module with the repository using `diff`. The existing
   declarations retain byte-for-byte signatures and visibility; only the proof is
   decomposed into two new intermediate declarations. No target statement or definition
   changed.
2. PASS: compiled the module with `lcompile.py`. It compiles successfully and contains no
   forbidden declaration forms. The only remaining `sorry`s are the two named split
   theorems; the bijectivity theorem is proved from them. The split theorems are the
   explicitly recorded open obligations, so their `sorryAx` is expected until discharged.
3. PASS: checked the split statements on the zero-ring and one-minimal-prime cases. They
   are the injectivity and surjectivity components of the unchanged bijectivity statement,
   hence true and strictly simpler. No hollow definition or extra hypothesis was added.
4. PASS: reviewed the proof route and imports. The component theorem now uses exactly the
   injectivity and surjectivity declarations; all existing imports remain needed by the
   total-fractions construction. The unit route is preserved: the finite-product
   decomposition remains the stated route, with no bypass. No imports or modules were
   pruned.
5. PASS: updated the existing DAG node's proof and `proof_deps` to match the Lean proof,
   and verified that both new nodes record their declarations, source, blueprint, and
   split status. The original bijectivity signature and the total-fractions statement are
   unchanged.

Changed: removed one linter-triggering blank line, synchronized the existing DAG node with
its decomposition, and added this second-reading record. Closed the original bijectivity
hole; added the two named holes `fractionRing_pi_injective_of_compatible` and
`fractionRing_pi_surjective_of_compatible`, nodes
`lem-weil-pbc-fraction-ring-pi-injective` and
`lem-weil-pbc-fraction-ring-pi-surjective`.
