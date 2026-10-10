# Stage 1 delivery: lem-galois-fpqc-descend-open-immersion

## Files written

- `dag/nodes/sec-curve-estimates/lem-galois-fpqc-descend-open-immersion.json`: split statement, five proof steps.
- `dag/nodes/sec-curve-estimates/lem-galois-open-immersion-affine-descent.json`: new statement, Mathlib leaf. It is the affine flat-surjective case of Stacks 02L3 and specializes Mathlib's `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'` because a morphism of affine schemes is quasi-compact.

## Attachments

None. The source Lean has no declaration stating the family-form item.

## WANTED

None. The project checkout lacks the rebuilt `literature/stacks-project` directory; I read the matching Stacks source in `/home/ubuntu/c1-stacks-review/descent.tex`, including lines 5862-5912, and checked its tag table. The cited document is `literature/stacks-project/descent.tex` as specified by the project.

## Corrections

The imported item had no proof. I retained its statement and its four statement dependencies. The generic fpqc local criterion 02KP is already a node, so the split verifies its four conditions for open immersions. The affine case is recorded as a Mathlib leaf rather than reproducing Stacks' last paragraph: Mathlib's 02L3 instance says exactly that case after the affine morphism is recognized as quasi-compact.

## Review by C1

I read Stacks Descent 02L3, including its proof and its concluding invocation of the general descent criterion 02KP, and checked the labels 02L3, 02KP, 02KO and 01JY in the Stacks tag table. The item is the descent direction of 02L3 for an fpqc covering, and the new node is the affine flat-surjective case explicitly begun in the second paragraph of that proof. I read Mathlib `FlatDescent.lean` lines 130-140: its `IsOpenImmersion.DescendsAlong (Surjective ⊓ Flat ⊓ QuasiCompact)` applies to the new node's fibre-product square. The affine source and target make the flat surjection quasi-compact. The new node has a complete standalone statement, no proof sketch, and its notions cite their defining nodes. I searched the DAG and blueprint for the affine case and found no equivalent node; I also checked the Lean source for the item tag and the descent declaration. Existing Mathlib searches on the item cover the family form and the single-morphism candidate.

In Step 1, `def-weil-open-immersion` supplies the topological and sheaf conditions transported under isomorphisms, as required by 02KO. In Step 2, the same definition and `def-pc-fibre-product` identify an arbitrary pullback of an open subscheme with an open subscheme; this is the base-change fact cited by 02L3 as Schemes 01JY. In Step 3, the open image and inverse maps agree on target-open overlaps, so the defining conditions glue; this is the Zariski locality asserted in 02L3. Step 4 uses only the statement of the new affine-descent leaf, with exactly affine base schemes, flatness, surjectivity, and an open-immersion base change, to verify condition (3) of `lem-weil-pbc-fpqc-local-on-base-criterion`. Step 5 uses the *statement* of that 02KP node, with conditions (0)-(3) already established and the given fpqc covering, to conclude the item. This generic criterion is an off-unit tool and is declared in `split_report.tool_uses`.

I checked empty base and empty source: the empty scheme is affine, and an empty open subscheme base change has the expected open-immersion behavior. For the nonempty affine case the only extra hypothesis in the Mathlib instance is quasi-compactness of `S' → S`, automatic for a morphism between affine schemes. A family need not consist of quasi-compact morphisms, which is why the item itself remains split and invokes 02KP. No statement was weakened, and no new node restates the item.
