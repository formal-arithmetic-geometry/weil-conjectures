# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-zl-finite-fp-proetale-pushforward-exact.json`: five-step split of the existing Stacks Tag 09A8 item; no new DAG nodes and no Mathlib leaves.
- `citations.json`: verbatim full statements for every node used by every proof step.
- `report.md`: this review and delivery record.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id, the blueprint tag, and finite pro-etale pushforward declarations. No sorry-free project declaration states the complete result. The existing etale finite direct-image theorem is a different site and is not an attachment.

## WANTED

None. The Stacks source and all cited DAG statements are present locally.

## Audit of the imported item

The statement is retained exactly, including finite plus locally finite presentation, the small pro-etale site, arbitrary abelian sheaves, and the arbitrary ringed-module consequence. The item had no proof and no split report. The current source is Stacks Tag 09A8 (`proetale.tex`, label `lemma-finite`), whose proof is the affine w-contractible evaluation argument. The module assertion is the immediate underlying-abelian consequence described in the source. The inherited `blueprint.from` points to the parent `lem-zl-finite-pushforward` sentence that requires ambient pro-etale exactness before the coefficient tower; I filled its proof and split metadata without changing the statement.

The exactness argument uses the existing generic infrastructure. Finite plus locally finite presentation gives finite presentation (`lem-trf-finite-morphism-finite-presentation`). On an affine target, the w-contractible ind-etale faithfully flat cover is supplied by `lem-weil-pbc-source-wcontractible-extension`; finite base change is `lem-weil-pbc-finite-morphism-permanence`; and Tag 0986 is already stated as `lem-ce-finite-finitely-presented-wcontractible`. The direct-image section formula comes from `def-weil-proetale-inverse-image`. Exact evaluation on the resulting affine w-contractible object comes from `lem-weil-pbc-source-affine-wcontractible-evaluation`, with the sheaf epi/local-lifting criterion supplied by `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`. The module clause uses the intrinsic direct-image definition, the ringed-topos module adjunction, and the faithful exact forgetful functor.

## Review by Q33

I read the current item, its chapter `sec-deligne-laumon-a1`, unit `sk-thm-dl-a1-upper`, the parent `lem-zl-finite-pushforward`, and both the master and main-20261015 blueprint references. I read Stacks `proetale.tex` Tag 09A8 in full, including the preceding Tag 0986 proof of finite finitely presented algebras over w-contractible rings. I also opened every cited node and copied its complete statement into `citations.json`; each quotation is therefore a verbatim statement, and each cited statement supplies the fact named by its step.

Step 1 checks the finite-morphism and locally-finite-presentation hypotheses against `lem-trf-finite-morphism-finite-presentation`, then uses the pro-etale site's weakly etale objects and fpqc covers for the affine-local reduction. Step 2 checks that the selected cover ring is ind-etale and faithfully flat, that its affine spectrum is a pro-etale cover, and that the finite pullback algebra is finite and finitely presented. The cited Tag 0986 node explicitly allows the zero algebra, so empty fibres are covered. Step 3 computes the direct-image sections as sections on `Spec(D tensor_A B)` and uses the cited weakly-contractible evaluation theorem plus the epi/local-surjectivity criterion to obtain exactness. Step 4 turns those local computations into a short exact sequence of sheaves, using the sectionwise kernel formula and the same epi criterion. Step 5 checks the arbitrary ringed-module case: the direct image has the action through `f^{-1}R_Y -> R_X`, and the cited forgetful-functor statement is faithful and exact, so underlying abelian exactness reflects to modules.

I tested the identity map (the tensor pullback is the same w-contractible object), the empty source/zero finite algebra (all evaluated sheaves are zero), a finite disjoint union of copies of the target, and a nonreduced finite algebra. I checked that no step assumes flatness, torsion, constructibility, or a finite coefficient ring. No step exceeds 2000 characters. No SGA source is cited and no forbidden route is used.

## Not duplicates

lem-zl-finite-fp-proetale-pushforward-exact vs lemma-weil-pbc-finite-direct-image-exact: the existing node is exactness on small étale abelian sheaves, whereas this item is exactness on small pro-etale sheaves for finite locally finitely presented morphisms.

lem-zl-finite-fp-proetale-pushforward-exact vs lem-weil-proetale-module-direct-image-left-exact: the existing node proves only left exactness for constant-ring module sheaves; this item proves epimorphism preservation for abelian sheaves and then arbitrary ring-sheaf modules.

lem-zl-finite-fp-proetale-pushforward-exact vs lem-exc-proetale-closed-exact: the existing node treats closed immersions on the pro-etale site in its supported coefficient setting; this item treats every finite locally finitely presented morphism and all abelian sheaves.

## Generic tools for maintainer assessment

The split report declares the finite-presentation, w-contractible cover, finite base-change, Tag 0986, affine evaluation, epi criterion, and module-forgetting nodes as generic infrastructure from other units. They supply site and scheme facts that this affine exactness route uses; no unit-specific route is replaced.

## Unfinished work

No stage-1 part remains open. No Lean files were written or compiled, and no live project or launcher files were modified.
