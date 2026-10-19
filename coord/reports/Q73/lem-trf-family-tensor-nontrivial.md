Files written:

- `dag/nodes/sec-trace-formula/lem-trf-family-tensor-nontrivial.json` — split statement.
- `dag/nodes/sec-trace-formula/lem-trf-finite-family-tensor-nontrivial.json` — statement-only auxiliary lemma; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-family-coproduct-finite-filtered.json` — Mathlib leaf, `CategoryTheory.Limits.CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone`, `Mathlib/CategoryTheory/Limits/Constructions/Filtered.lean:103`.
- `dag/nodes/sec-trace-formula/lem-trf-flat-tensor-preserves-injection.json` — Mathlib leaf, `Module.Flat.lTensor_preserves_injective_linearMap`, `Mathlib/RingTheory/Flat/Basic.lean:131`.
- `citations.json` records a verbatim statement quote for every node used by every proof step.

Attachments: none. The project source contains no declaration tagged `(blueprint: lem-trf-family-tensor-nontrivial)` or any exact finished declaration for this statement; the nearby common-extension declaration depends on this item and therefore is not an attachment.

WANTED: none.

## Not duplicates

- `lem-trf-finite-family-tensor-nontrivial` vs `lem-trf-family-tensor-nontrivial`: the new node is restricted to finite index sets and is a strict auxiliary induction input; the existing item concerns arbitrary small families and the full coproduct.
- `lem-trf-finite-family-tensor-nontrivial` vs `lem-trf-family-common-extension-field`: the new node proves nontriviality of finite tensor coproducts; the existing node constructs a common field extension from the arbitrary-family coproduct.
- `lem-trf-finite-family-tensor-nontrivial` vs `lem-trf-infinite-product-surjective`: the new node is a finite tensor nontriviality lemma; the existing node is a product-surjectivity statement whose Tag 0CNJ proof uses common-field constructions.
- `lem-trf-finite-family-tensor-nontrivial` vs `lem-weil-common-extension-fields-tensor-nontrivial`: the new node treats an arbitrary finite family and includes the empty family; the existing node treats exactly two extensions.
- `lem-trf-family-coproduct-finite-filtered` vs `lem-weil-pbc-commutative-algebras-colimits-exist`: the new node identifies a coproduct with the filtered colimit of its finite subcoproducts; the existing node only asserts existence of arbitrary small colimits.
- `lem-trf-flat-tensor-preserves-injection` vs `lem-weil-common-extension-fields-tensor-nontrivial`: the new node is the generic flat-module injection theorem; the existing node is a nontriviality result for a binary tensor of fields.

## Review by Q73

I read the imported item and the adjacent `lem-trf-family-common-extension-field` node. The latter invokes this item, so I did not use it and avoided a cycle. I checked the finite-family statement against the finite-subfamily paragraph of Stacks `limits.tex`, Tag 0CNJ, and checked the categorical filtered-colimit statement against Mathlib's `isColimitFiniteSubproductsCocone` declaration. I also read the exact Mathlib source for `Module.Flat.lTensor_preserves_injective_linearMap` and recorded its actual line.

Step 1 uses the finite-family statement for each finite subset and the flat-tensor injection statement for the transition map. The structural map from the base field into each finite tensor factor is injective because its kernel is an ideal of a field and the target is nontrivial; I explicitly checked that this argument includes the empty complement. The factorization of a larger finite tensor as the smaller tensor with the complementary finite tensor is the standard associativity/unitor identification. Step 2 uses the filtered finite-subcoproduct colimit theorem and the existing commutative-algebra colimit existence node; the hypotheses are met because the family is small and the category is commutative $k$-algebras. Step 3 uses the disjoint-union presentation of a filtered colimit: injective transition maps keep $0$ and $1$ from the empty stage distinct. I separately checked $J=\\varnothing$, where the sole stage is $k$ and the coproduct is canonically $k$.

I ran all required Mathlib searches for the item and each new node with `msearch.py`; the finite-family search found only binary/generic flatness results, while the two categorical/flatness nodes matched the declarations recorded above. No Lean files, compilers, Lake, or build tools were used.

What was wrong in the imported node: it had no proof and its intended nearby common-extension proof was circular. The split replaces that route with finite tensors, their filtered colimit, and injective transition maps.

What remains unsplit is the finite-family tensor lemma; it is a genuine strict sublemma rather than a restatement of the arbitrary-family item and is queued for a later worker.
