## What changed

Filled the proof of `AlgebraicGeometry.Scheme.depth_two_pushforward_coherence`.
The proof uses two strictly smaller intermediate results: the coherent depth-two
module extension and the Hartogs algebra comparison. Added proof-only imports for
those modules and updated the target node's proof dependencies and proof steps. The interface change record is `coord/changes/depth_two_pushforward_coherence.md`.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.depth_two_pushforward_coherence`.
The two imported intermediate declarations remain named `sorry` theorems:
`AlgebraicGeometry.Scheme.exists_depth_two_coherent_module_extension`
and `AlgebraicGeometry.Scheme.depth_two_hartogs_algebra_comparison`; each has its
own node and complete source proof description.

## No longer needed

None. The private linear-equivalence depth lemma and both intermediate results
are used by the proof.

## Where the brief, the DAG or earlier work was wrong

The original target node had an empty `proof_deps` list even though its Lean proof
requires the two intermediate results. The node has been updated to record those
dependencies and the three proof steps now name their uses.

## New nodes

Added `lem-sbc-depth-two-coherent-module-extension` for the affine double-dual
extension theorem and `lem-sbc-depth-two-hartogs-algebra-comparison` for the
Hartogs comparison theorem. Their modules are included in this delivery.

## Earlier second reading (a previous round; superseded)

Second reader: M3 worker review of the target and both intermediate nodes.
The target statement is unchanged. The proof applies the coherent extension
result to obtain `N`, then the Hartogs comparison to obtain the global module
isomorphism and stalk linear equivalences; the finite affine and depth claims
are transferred by isomorphism. Both added statements are strict sub-results
with independent source descriptions, and the unit route through the target
is retained.

## Second reading by M3

1. **Interface unchanged.** Compared the delivered target module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports, a private helper, and the target proof differ. Verdict: pass.
2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`; there are no errors, forbidden declarations, or `sorry` in definitions. The target proof closes `depth_two_pushforward_coherence`; the two explicitly split intermediate theorems remain the named `sorry` declarations listed above. The private depth transport argument uses only linear equivalence and finite-module facts. Verdict: pass.
3. **Split statements.** Checked both new declarations against their node files and source descriptions. The coherent extension and Hartogs algebra comparison are strictly smaller prerequisites, are true at the stated strength, and are not duplicates of declarations found in the library. Their docstrings give complete source-level proof descriptions and matching nodes. Verdict: pass.
4. **Pruning and route.** The target imports both intermediate modules because the proof applies both declarations; the finiteness import supports the finite-module transport. No prior proof dependency is unused, and the unit route remains represented by the target and its two prerequisite nodes. Verdict: pass.
5. **DAG agreement.** The target node proof steps and `proof_deps` match the declarations actually applied, and each new node has matching Lean metadata, source, blueprint, and split status. Verdict: pass.

Changed after this reading: added this review section only; no Lean statements or proofs were altered.
