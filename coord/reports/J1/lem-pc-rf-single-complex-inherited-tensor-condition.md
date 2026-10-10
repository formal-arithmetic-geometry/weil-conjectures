Files written:

1. `dag/nodes/sec-picard-framework/lem-pc-rf-single-complex-inherited-tensor-condition.json` (statement, split proof, metadata).
2. `dag/nodes/sec-picard-framework/lem-pc-derived-tensor-transitivity.json` (statement-only unsplit node; Mathlib has only ordinary tensor generalizations).
3. `citations.json`.

Attachments: none. No project declaration with this blueprint tag or exact statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

WANTED: `literature/stacks-project/perfect.tex`, Tag 0DJA, for the source proof text; the repository has the citation index but not the TeX source. The online Stacks page confirms that the proof computes source and target using tensor transitivity (Tag 15.60.15).

## Not duplicates

`lem-pc-derived-tensor-transitivity` vs `lem-pc-rf-single-complex-inherited-tensor-condition`: the new node is a generic derived-tensor associativity statement for complexes over rings, sourced to Tag 15.60.15; the existing node is the scheme-level inherited stalkwise base-change conclusion of Tag 0DJA and does not state generic tensor transitivity.
`lem-pc-derived-tensor-transitivity` vs `lem-pc-rf-base-change-single-complex-criterion`: the new node is a generic derived-tensor associativity statement for complexes over rings; the existing node is a scheme-level derived direct-image base-change criterion and does not state tensor transitivity.

## Review by J1

I read the item node, its ancestor `lem-pc-rf-perfect-base-change`, and the existing dependent node `lem-pc-rf-base-change-single-complex-criterion`. The item statement matches Stacks Tag 0DJA(1): a cartesian square, a map `L(g')^*K -> K'`, the pointwise cohomology condition, and inheritance after tensoring with arbitrary `E`. I searched the source checkout for the item id, blueprint tag, and the Stacks identifiers; no sorry-free declaration states it. I also checked the online Tag 0DJA page, whose proof explicitly invokes the transitive property of tensor product.

The sole proof step fixes an arbitrary `x'`, introduces the four stalk rings, and applies the new node to identify the source and target of the inherited stalk map with the original map tensored by `E_x`. The cited node states exactly that derived-tensor identification and its naturality. No additional hypothesis is introduced: the argument uses only the item hypothesis and arbitrary `E`; `x'` and the cohomological degree are then discharged by arbitrariness. The step is marked non-elementary because the derived tensor transitivity is a genuine homological-algebra lemma.

For the new node I checked the statement on the zero complex and on ordinary modules concentrated in degree zero; it reduces to the usual associativity/base-change isomorphism. I searched the whole DAG and blueprint for tensor transitivity and for Tag 15.60.15 before creating it. The recorded LeanFinder hits are ordinary module tensor identities, not derived-category results; Loogle and Mathlib grep found no match, and LeanSearch was unavailable. The new node therefore remains statement-only and unsplit. The item metadata records the ancestor blueprint place and the proof step that realizes it.

What was corrected: the imported item had no proof, no proof dependencies, and status `unsplit`; these were replaced by the Tag 0DJA stalkwise proof, the single generic dependency, `proof_origin`, and `status: split`. No source statement was changed.

## Second reading by J1

- Item statement: checked against `/home/ubuntu/c1-stacks-review/perfect.tex`, Tag 0DJA, `lemma-single-complex-base-change-condition-inherited`, part (1); the cartesian-square, derived-category, stalkwise, and arbitrary-$E$ hypotheses and conclusion agree.
- Step 1: checked against the local stalk computation in Tag 0DJA; the introduced stalk rings and formation of the pulled-back stalk complex are elementary from the displayed base-change definitions.
- Step 2: checked against Tag 0DJA's transitivity paragraph and More on Algebra Tag 0BYJ (`more-algebra-lemma-triple-tensor-product`); the cited node supplies exactly the derived-tensor associativity and naturality used, and the isomorphism argument is valid for every stalk and degree.
- New node `lem-pc-derived-tensor-transitivity`: statement-only and self-contained with ring/module/complex hypotheses and definition dependencies; checked on zero complexes and degree-zero modules, and searched the DAG for duplicates before retaining it as an unsplit input. Its Stacks source was corrected to Tag 0BYJ, the actual tag for the cited triple-tensor lemma.

Changes made: corrected the non-tag source reference `15.60.15` to Stacks Tag `0BYJ` in the dependency source and proof citation; normalized the dependency statement and proof wording to the repository's derived-tensor TeX notation. The item's inherited `created` metadata names its original importing item and is maintainer-owned, so it is left unchanged by the delivery tool.
