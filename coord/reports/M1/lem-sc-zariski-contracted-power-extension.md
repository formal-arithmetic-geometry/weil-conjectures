1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-zariski-contracted-power-extension.json`: repaired the three-step split; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-zariski-contracted-power-torsor.json`: corrected statement-only supporting node; no Mathlib match.

2. Attachments

None. The slopmaster2 source has no declaration stating this contracted-power extension or the coherent integer-power torsor result.

3. WANTED

None. The contracted-power argument is the worker's own construction from the contracted-product notion in `lem-sc-torsor-h1`.

4. Problems found and repaired

The old supporting node falsely identified a product sheaf with a contracted power. For a trivial torsor with nonzero abelian group G and m=n=1, the proposed map G x G -> G is addition and has a nontrivial kernel. I replaced it by coherent isomorphisms from contracted products, including the inverse torsor and the evaluation T wedge T^{-1} -> G. Step 1 now uses these isomorphisms for addition, zero, inverse and the abelian-group laws; `lem-sc-torsor-h1` supplies only the definition of the contracted product. No edge points to `lem-sc-zariski-ext-torsor`, which depends on this item.

Stacks Cohomology of Sheaves Lemma 02FQ (`cohomology-lemma-torsors-h1`) constructs its extension as a pushout of 0 -> Ker(sigma) -> Z[T] -> Z -> 0 along Ker(sigma) -> G. It does not give the contracted-power construction. I corrected the item's `proof_origin`, all three step source places, the new node's source place, and the item source place to identify this as the worker's argument. The earlier report incorrectly attributed the construction to 02FQ.

5. What was checked

I read Stacks 02FQ for its actual pushout construction and the statements of `lem-sc-torsor-h1`, `def-sc-gm-torsor`, and `def-sc-topological-abelian-cohomology` for the notions this argument uses. The supporting node develops the contracted-product operation into coherent powers; it is not a statement from 02FQ. The proof remains within the ancestor blueprint's representative-level torsor construction. The supporting statement is self-contained and unsplit. The recorded Mathlib searches and the prior whole-DAG, blueprint and Lean-source search found no existing node or declaration giving its full statement.

## Review by M1

The returned false statement failed already for X a point and T=G trivial: G x G cannot be identified with G by addition when G is nontrivial. With the corrected contracted product, the same test gives G wedge G isomorphic to G by addition, and G wedge G^{-1} maps to G by difference. The n=0 and n=1 cases give the unit torsor and T; negative n uses the opposite action. These checks exercise each sign case of the new statement.

In step 1, `lem-sc-torsor-h1` states that the contracted product is the antidiagonal quotient. The corrected supporting node states the maps mu_{m,n}, the inverse-power pairing, and their unit, associativity and commutativity laws, exactly what step 1 uses. The local-section formula a+b=mu_{m,n}([a,b]) descends through the quotient and glues; the inverse section is unique because pairing with a is an isomorphism of torsors. Step 2 cites that same node for the torsor status of every power and addition of degrees, `def-sc-gm-torsor` for local nonemptiness, and `def-sc-topological-abelian-cohomology` for the abelian-sheaf sequence. Local surjectivity is checked on a cover where the integer section is constant, refining to a section of that power; the kernel is the degree-zero summand on local sections. Step 3 cites the supporting node's explicit T^{otimes 1}=T and its unit action, so the fibre over 1 has the original G-action.

I checked the hypotheses at each use: X carries the small Zariski site, G is abelian for the swap coherence and abelian-sheaf structure, and T is a Zariski G-torsor for local triviality and the unique difference section. The source attribution and C4 failures in the return are repaired. The citation audit quotes the exact revised statement fragments. The corrected supporting node has no proof steps of its own, and its statement is strictly narrower than the extension: it supplies coherent powers but makes no extension or exactness claim.
