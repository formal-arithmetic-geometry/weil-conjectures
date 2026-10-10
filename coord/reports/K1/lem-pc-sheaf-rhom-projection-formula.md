Files written:

- `dag/nodes/sec-picard-framework/lem-pc-sheaf-rhom-projection-formula.json` — statement split, no new child nodes, Mathlib searches found no exact derived comparison.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

Attachments: none.

WANTED: `literature/stacks-project/cohomology.tex`, Remark `remark-projection-formula-for-internal-hom`, for the source text of the construction; the checkout contains only the imported node metadata.

The item had no exact sorry-free declaration in `WeilConjectures`. Its imported statement is retained. I searched the DAG for the internal-Hom projection comparison and found no duplicate; the nearby `lem-pc-qcqs-sheaf-rhom-adjunction` correctly uses this item as its first-arrow construction. I did not create a child node because the comparison itself is the item's clause, while the adjunction, tensor-Hom bijection, and pullback-tensor comparison already have existing nodes.

## Review by K1

I read the item, its blueprint ancestor `lem-sc-finite-duality`, and the source references attached to the imported statement. I also read the complete statements of `lem-pc-ringed-spaces-derived-adjoint-general`, `lem-sc-derived-internal-hom-adjunction`, and `lem-pc-derived-pullback-tensor-product`. Step 1 uses the first node for the derived pullback/direct-image adjunction and the second for the canonical tensor-Hom bijection and evaluation construction; both statements explicitly provide those facts. Step 2 tests against an arbitrary object of `D(O_Y)`, uses the counit from the adjunction, applies the stated pullback-tensor isomorphism, and transposes with the stated tensor-Hom bijection; each cited statement says exactly the operation used. Step 3 uses the naturality clauses in all three statements to justify naturality in `L` and `M`, and preserves the item's explicit absence of an isomorphism claim. The hypotheses are checked at every use: `f` is a scheme morphism, all objects lie in the derived categories named by the item, and the pullback-tensor node is applied with `g=f`. I tested the identity-morphism edge case conceptually: the unit/counit are identities and the construction reduces to the ordinary evaluation transpose. I corrected the initial proof sketch to spell out the arbitrary-test-object mate construction, avoiding an uncited projection-formula assertion. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; only underived sheaf adjunctions were found, and LeanSearch was unavailable.

What could not be finished: the cited Stacks source file is not present in this checkout, so the proof origin records an agent reconstruction from the imported reference and existing DAG statements.

## Second reading by K1

- Item statement: checked against the imported Stacks reference `remark-projection-formula-for-internal-hom` and the definitions cited in the node; the canonical morphism and absence of an isomorphism claim are retained.
- Step 1: checked against the complete statements of `lem-pc-ringed-spaces-derived-adjoint-general` and `lem-sc-derived-internal-hom-adjunction`; the unit/counit and evaluation data used are stated there.
- Step 2: checked against the complete statements of `lem-pc-ringed-spaces-derived-adjoint-general`, `lem-sc-derived-internal-hom-adjunction`, and `lem-pc-derived-pullback-tensor-product`; repaired the mate direction by testing a map `A -> Rf_*RHom_X(L,M)`, applying the adjunction, then the tensor comparison and counit.
- Step 3: checked against the naturality clauses of all three cited statements; the construction is functorial in `L` and `M` and asserts no invertibility.
- New nodes: none; there are no child-node statements requiring B1-B7 or duplicate-node review.
- Edge cases: the identity morphism reduces to the ordinary evaluation transpose; zero objects give the zero morphism; no extra hypotheses are introduced.
- Mathlib search record: the existing LeanFinder, Loogle, grep, and unavailable LeanSearch entries were checked against `searches.jsonl`; no exact derived comparison declaration was found.

Changes made: corrected Step 2's reversed mate construction and made the Yoneda test map explicit, because the original text started with a map in the wrong direction; appended this second-reading audit.
