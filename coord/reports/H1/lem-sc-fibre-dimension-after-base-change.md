Files written:

- `dag/nodes/sec-picard-framework/lem-sc-fibre-dimension-after-base-change.json`, repaired statement split.

Attachments:

None. The Lean source search found no declaration tagged `(blueprint: lem-sc-fibre-dimension-after-base-change)` and no declaration stating this result.

WANTED:

None. The source is Stacks, `literature/stacks-project/morphisms.tex`, Tag 02FY (1); its dimension assertion explicitly cites Algebra, Lemma 00P4 (`literature/stacks-project/algebra.tex`, line 28307).

What was wrong and changed: the former identification node restated the first clause of the item, so I deleted it and wrote the factorisation through residue fields and the fibre-product calculation in step 1. The former local-dimension node duplicated the existing `lem-weil-pbc-dimension-at-point-field-extension` (the 00P4 route), so I deleted it and used that existing node in step 2. I also added `lem-weil-pbc-lft-base-change`, since local finite type of the fibre is a separate base-change fact. The tool use is declared for the generic 00P4 node as required.

What I could not finish: no Lean changes are required at stage 1; the source checkout is represented by the repository's Stacks source paths and the cited line/tag.

## Review by H1

I read the item source as Morphisms Tag 02FY (1), including its reference to Algebra Lemma 00P4, and checked the item hypotheses against the definitions named in `stmt_deps`. I searched the Lean source, the full DAG, and the blueprint before retaining any helper; the only reusable statements needed are the existing cartesian-square pasting node, the Mathlib base-change leaf, and the existing 00P4 dimension node.

Step 1 now carries the actual argument: `def-weil-residue-field` supplies the residue-field factorisation, the fibre and fibre-product definitions expand the four expressions, and `lem-weil-pbc-cartesian-square-pasting` supplies the non-elementary transitivity of pullbacks. Step 2 first uses `lem-weil-pbc-lft-base-change` to establish that `X_s` is locally of finite type, then uses `def-kun-dimension` for invariance under open restriction and `lem-weil-pbc-dimension-at-point-field-extension` for the affine field-extension comparison. Its statement is the existing 00P4 result, so this off-unit generic tool is declared in `split_report.tool_uses`.

I checked the hypotheses at both steps: `s = g(s')`, the residue-field map is the one induced by the point, the affine chart has a finite type `kappa(s)`-algebra, and the prime at `x'` contracts to the prime at `x`. Small checks are `Spec K` (dimension zero) and `A^1_K` (dimension one) after arbitrary field extension. The repair removes both relabelling/duplicate nodes and the unavailable-source wording, and adds the previously missing finite-type base-change citation.
