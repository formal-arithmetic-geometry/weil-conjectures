Files written:

- `dag/nodes/sec-curve-estimates/lem-exc-etale-field-galois-classification.json`: statement item, split into three sourced steps.
- `dag/nodes/sec-curve-estimates/lem-exc-etale-open-subgroup-fixed-field.json`: statement-only unsplit node; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-exc-etale-finite-subextension-fixing-subgroup-open.json`: Mathlib leaf, exact `IntermediateField.fixingSubgroup_isOpen`.
- `dag/nodes/sec-curve-estimates/lem-exc-etale-algebraic-endomorphism-bijective.json`: Mathlib leaf, exact `Algebra.IsAlgebraic.algHom_bijective`.
- `dag/nodes/sec-curve-estimates/lem-exc-etale-embedding-extension-sepclosed.json`: Mathlib leaf, exact `IntermediateField.exists_algHom_of_splits`.
- `dag/nodes/sec-curve-estimates/lem-exc-etale-galois-fixed-field-subgroup.json`: Mathlib leaf, exact `InfiniteGalois.fixedField_fixingSubgroup`.

Attachments: none.

WANTED: none.

The item was unsplit and has no sorry-free declaration in the slopmaster2 source. I deleted the separable-degree leaf because its `finSepDegree` statement counts embeddings into an algebraic closure and did not directly justify embeddings into `K^sep`. Step 1 now proves finiteness elementarily from a finite basis, proves nonemptiness by the embedding-extension leaf, and adds separate Mathlib leaves for bijectivity of the extended endomorphism and openness of a finite-subextension fixing subgroup.

## Review by E1

I reread `pione.tex` at Tags 03SF and 03QR and checked the item against the finite Galois correspondence. For return point 1, step 1 now cites the exact statement of `IntermediateField.fixingSubgroup_isOpen`; the declaration name is removed from the prose. For point 2, it cites `Algebra.IsAlgebraic.algHom_bijective` and spells out why its algebraic-extension hypotheses hold for `K^sep/K`, so the extended map is an automorphism. For point 3, nonemptiness is proved by `exists_algHom_of_splits` with `E=L` and the inclusion of K. For point 4, the incorrect separable-degree leaf is deleted and finiteness is proved from a finite K-basis and finitely many roots. For point 5, step 1 explicitly establishes that `K^sep/K` is separable algebraic and normal, hence Galois, and the fixed-field node states only the Galois hypothesis required by its Lean declaration. Step 2 cites the existing open-subgroup node for exactly its fixed-field, subgroup, and finite discrete-coset clauses, then uses step 1 to identify the embedding G-set with G/H. Step 3 proves injectivity directly and proves surjectivity by choosing sigma_0, applying equivariance to stabilizers, and using the fixed-field identity; transitivity from step 1 then gives equality on all embeddings. I checked every quote in `citations.json` is verbatim in its cited node and removed the report's former claim about maintainer-filled metadata. I also checked edge cases K separably closed, L=K, and finite Galois L/K.

I verified that every cited quote is verbatim in `citations.json`, that all three new nodes are statement-only, and that their statements introduce K, K^sep, G, and the finite separable hypotheses instead of relying on unstated context. I tested the edge cases K separably closed (G trivial and the embedding set is a singleton), L=K, and a finite Galois extension (the set is G/Gal(K^sep/L)); these agree with all three clauses. No source or Lean declaration was found for a narrower attachment, and no hypotheses were added or dropped.

What I could not finish: no mathematical proof was formalized in Lean, as stage 1 requires only the natural-language DAG split.
