# lem-weil-pbc-matching-object-fibre-product

## Worker delivery

Files written: `dag/nodes/sec-curve-estimates/lem-weil-pbc-matching-object-fibre-product.json` and this report. No new nodes or Lean attachments. The item is split into four steps: degree zero, the natural bijection between cones to the product boundary diagram and pairs of cones, the induced matching-scheme isomorphism, and compatibility with the matching maps.

Source checked: pinned Stacks `simplicial.tex`, Tag 018D, `lemma-cosk-fibre-product` (proof omitted), with the hom-set proof of Tag 018C, `lemma-cosk-product`; `hypercovering.tex`, Tag 01GH, `lemma-funny-gamma`, proof, second paragraph. The local `/tmp/c1-lead-current/literature/stacks-project` checkout contains empty directories, so I read the `.tex` at the `a04446e57ec1fbc252a871afcec7752fb2807b14` commit through GitHub's raw source and verified the three tag-to-label pairs against `tags/tags`. No document is wanted.

Source/Mathlib audit: `grep -rn '(blueprint: lem-weil-pbc-matching-object-fibre-product)' /home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and a matching-object concept search found no declaration; the node's `lean_audit.slopmaster2.state` is `none`. Existing Mathlib searches were checked against `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:330` (`coskAdj`) and `Mathlib/CategoryTheory/Adjunction/Limits.lean:207` (`rightAdjoint_preservesLimits`); these do not identify the augmented matching scheme or state the item's comparison. The whole-blueprint search for `matching object fibre product` returned no other blueprint node.

The proof uses only the statements of `def-weil-pbc-finite-split-hypercover` (matching scheme as a limit) and `def-pc-fibre-product` (universal property and induced maps). For a test scheme over X, each compatible boundary family into the termwise fibre products is uniquely a pair of compatible boundary families into U and V. This works for n=1 (two vertices) and all higher n; n=0 is the diagonal isomorphism X to X times over X X. Each face component of the W matching map projects to the corresponding U and V face components. No hypercover covering hypothesis, qcqs hypothesis, or extra object is used.

`tools/review_split.py lem-weil-pbc-matching-object-fibre-product`: PASS, 0 new nodes; its unit `sk-prop-h2` has no realization recorded yet. `tools/check_dag.py`: 0 cycles and 0 self-loops; exits nonzero for 7 existing reach warnings and 11 route warnings on other nodes. No warning concerns this item.

The Stacks proof of 018D is omitted; the calculation above supplies it. I found no statement error in this item. Nothing remains unfinished in the split.

## Review by C1

I read the pinned Stacks `simplicial.tex` at Tags 018C (`lemma-cosk-product`) and 018D (`lemma-cosk-fibre-product`), and `hypercovering.tex` Tag 01GH (`lemma-funny-gamma`). Tag 018D states preservation of fibre products by coskeleton but omits its proof; 018C gives the hom-set argument, and 01GH applies the fibre-product matching target. The item states the resulting finite boundary-limit claim for augmented simplicial schemes over one base. There are no new nodes, so B's new-node checks are vacuous; its existing blueprint and Lean audit remain intact.

For C, I opened `def-weil-pbc-finite-split-hypercover` and `def-pc-fibre-product`. The former explicitly defines matching schemes as finite limits and says `M_0=X`; the latter gives the universal property, induced morphisms, and uniqueness of maps into fibre products. Step 1 uses these for `X ×_X X ≅ X`. Step 2 writes both directions of the cone bijection and verifies compatibility after both projections. Step 3 applies precisely those two universal properties to obtain inverse scheme maps, with naturality identifying the canonical comparison. Step 4 checks each boundary component of the matching map under the comparison. These steps prove the claim rather than moving it to a new node (D), and no dependency cycle is introduced.

For E, a test object and every boundary term are over the same `X`, which makes the paired cone maps land in each fibre product; without that common base the conclusion would fail. The `n=0` case is handled separately, and `n=1` reduces to pairs of vertices over `X`. No covering or finiteness assumption is used beyond existence of the stated matching limits. I asked the worker to verify the exact pinned Stacks labels after its local TeX checkout was empty; it did, and I independently read the pinned source here. No further correction was needed.
