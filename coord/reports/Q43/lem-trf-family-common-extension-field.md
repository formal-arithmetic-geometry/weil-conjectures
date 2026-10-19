# Stage 1 report: lem-trf-family-common-extension-field

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-family-common-extension-field.json` — statement split, no Mathlib leaf.
- `dag/nodes/sec-trace-formula/lem-trf-family-tensor-nontrivial.json` — statement-only helper, no Mathlib leaf.
- `citations.json` — verbatim citations for every non-elementary proof-step use.

Attachments:

- `Field.exists_common_extension` belongs to the existing node `lem-weil-common-extension-fields` for the two-factor case; it does not state this arbitrary-family item.

WANTED:

- None. The Stacks source and the existing Mathlib/DAG colimit and residue-field ingredients are available.

The project source contains no declaration tagged `(blueprint: lem-trf-family-common-extension-field)` and no sorry-free declaration with the item's arbitrary-family statement. The existing `Field.exists_common_extension` declaration handles only two extensions, so I split the item.

The item follows the Tag 0CNJ construction. First, the existing colimit node supplies the small coproduct of the commutative k-algebras. The new helper records the genuinely additional algebra fact that this small tensor coproduct of field extensions is nontrivial; it is smaller than the item because it does not construct a quotient field or any embeddings. A maximal ideal and the field quotient are supplied by the existing reviewed Mathlib leaves. The quotient of each coproduct map is a unital map from a field to a nontrivial field, hence injective by the explicit kernel argument. Compatibility with k follows from the coproduct and quotient maps. The empty family is checked separately in the statements and proof text.

## Review by Q43

I read the imported item node, the Tag 0CNJ proof in `literature/stacks-project/limits.tex`, the existing two-extension node `lem-weil-common-extension-fields`, its maximal-ideal and quotient-field leaves, and the commutative-algebra-colimits node cited in Step 1. I also read the blueprint ancestor `lem-trf-local-term-locality` and the Tag 0CNJ use in `lem-trf-infinite-product-surjective`. Step 1 uses exactly the colimit existence asserted by `lem-weil-pbc-commutative-algebras-colimits-exist`; its hypotheses are met because the family is small and each field carries the given k-algebra structure. Step 2 uses exactly the new helper's assertion that the resulting coproduct is nontrivial, including the empty family. Step 3 uses the existing maximal-ideal statement for the nontrivial commutative coproduct and the existing quotient-field statement for its maximal ideal; these are precisely the two quotes recorded in `citations.json`. Step 4 is elementary: a nonzero element in the kernel of a unital map from a field is invertible, forcing the target to be trivial, and the k-algebra equalities give `e_j ∘ a_j = b`.

I searched the whole DAG and blueprint for arbitrary-family common-field, tensor-coproduct, and nontrivial-family statements. The only close DAG material is the reviewed pairwise common-extension construction and its two-factor tensor-inclusion/nontriviality leaves; those require exactly two factors and therefore do not duplicate the new small-family helper. The item itself is not a restatement of the helper: it additionally forms a maximal-ideal quotient and produces compatible field embeddings. I tested the empty family, a singleton family, and two extensions: the coproduct is respectively k, the given field, and the ordinary tensor product, and the quotient construction gives the expected common field. No statement was weakened, no SGA source was used, and no cycle is introduced; `proof_deps` is exactly the union of the step uses.

## Not duplicates

- lem-trf-family-tensor-nontrivial vs lem-trf-family-common-extension-field: the helper asserts only nontriviality of the small coproduct ring; the item additionally takes a maximal-ideal quotient and constructs compatible field embeddings.
- lem-trf-family-tensor-nontrivial vs lem-trf-infinite-product-surjective: the helper is an algebraic nontriviality statement for a coproduct of field extensions; the existing item is the geometric surjectivity conclusion for an infinite product of affine schemes and uses a common field as one proof step.
