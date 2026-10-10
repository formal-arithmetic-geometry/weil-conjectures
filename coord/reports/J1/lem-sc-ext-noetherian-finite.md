# Stage-1 report: lem-sc-ext-noetherian-finite

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-ext-noetherian-finite.json`: Mathlib leaf, `ModuleCat.finite_ext` at `Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean:27`.
- `citations.json`: empty because a Mathlib leaf has no proof steps or citations.

## Attachments

None. The match is a Mathlib declaration, not a project declaration.

## WANTED

`literature/stacks-project/algebra.tex`, Lemma 08YR, for `lem-sc-ext-noetherian-finite`. The local Stacks checkout is absent; I read the Stacks Project's published Tag 08YR page, including its statement and proof.

## Corrections and unfinished work

The item's previous Mathlib searches missed `ModuleCat.finite_ext`; the new Loogle and grep searches found it. The node's mathematical statement agrees with Stacks Tag 08YR. Its proof and dependency lists remain empty because it is now a leaf. No new node or proof remains to split for this item.

## Review by J1

I read the item's statement and the exact Stacks 08YR statement and proof. The theorem in pinned Mathlib takes a commutative Noetherian ring, two finite modules and a natural degree, and concludes that their `Abelian.Ext` is finite. `def-weil-pbc-noetherian-ring` defines Noetherian for commutative rings, `def-weil-finitely-generated-module` supplies the two finite-module hypotheses, and `def-pc-ext` defines Ext as the derived-category Hom identified by Mathlib's `Abelian.Ext`. The integer `q >= 0` is therefore the natural `i` in the declaration. I read `Finite.lean` lines 15-36 to verify all hypotheses and the conclusion. There are no proof steps to audit for citation coverage, so `citations.json` is empty. I also checked the small cases `q = 0` and `M = 0`: the instance proof treats degree zero directly, and zero is finite. The correction was replacing the stale negative Mathlib verdict with the exact declaration and its verified line.

## Second reading by J1

- Item statement: checked against Stacks Algebra, Tag 08YR (`lemma-ext-noetherian`); the Noetherian ring, finite module, all-degree Ext, and finite-module conclusion agree hypothesis by hypothesis.
- Source proof: checked the Tag 08YR proof, which uses a finite-free resolution and finite cohomology; as a Mathlib leaf this argument is encapsulated by the verified declaration rather than split into proof steps.
- New nodes: none; the item itself is the Mathlib leaf, so B1-B7 and citation coverage have no additional node or step to audit.
- Mathlib match: checked `ModuleCat.finite_ext` in `Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean:27` and surrounding lines 15-36; its `IsNoetherianRing`, two `Module.Finite`, and natural-degree hypotheses and `Module.Finite` Ext conclusion specialize exactly to the item.
- Edge cases: degree zero is covered by the declaration's zero branch; zero modules satisfy `Module.Finite`; fields are Noetherian and their finite modules satisfy the same instance; the empty-scheme case is vacuous because the statement is affine-module based.
- Searches: verified the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results in `searches.jsonl`; the positive Loogle and grep hits identify the same declaration.
- Metadata: retained the pre-existing `created.item` because it is a maintainer field on an existing item node and delivery preserves it.

Changes made: none to the mathematical split; this second reading records the source, declaration, dependency, and edge-case checks.
