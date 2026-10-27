## Worker report

Files written:
- dag/nodes/sec-smooth-purity/lem-pur-signed-twist-site-transport.json: item split into five steps; its statement and statement dependencies are unchanged.
- citations.json: one exact statement quotation for every step/node citation.

## New nodes

None. No Mathlib leaves are added. The mixed-sign calculation is an elementary step, rather than an artificial new lemma that repeats a clause of the item. Existing line-duality nodes supply the non-elementary existence and invertibility assertions.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, signed twist, Tate, and site transport found no declaration giving this entire statement. In particular no merely sorried or partial declaration is offered as an attachment.

## WANTED

None. This is an agent-written assembly and explicit basis calculation using the existing DAG statements. It does not assert that Stacks 07A4 proves finite Tate descent.

## Findings and changes

The imported item had no proof. Its statement is consistent with its fixed finite-coefficient conventions, including ramified E: ell^n annihilates O_E/varpi_E^n without any divisibility condition on n. I retained the specified root map, projection-induced theta, all nonnegative comparison maps, and the evaluation normalization of the negative maps. I did not change a target, add a geometric finiteness hypothesis, or invoke smooth purity.

Read the chapter sec-smooth-purity and unit sk-prop-a1-kummer. Read the current main-20261015 ancestor lem-pur-frame-independence and its proof, specifically Unit multiples and Permutations, and the corresponding older source recorded in the item ancestry. This auxiliary coefficient calculation supports those two operations through lem-pur-supported-cup-functoriality. The latter is a user of the item and is never cited, including indirectly through the later supported-twist definitions: doing so would create a cycle.

Mathlib searches were actually executed through batch2/msearch.py, with their exact queries retained in searches.jsonl and appended to the item's existing search history. The first Loogle query used an old MonoidalFunctor name and was rejected; I recorded that accurately and reran with Functor.Monoidal. The corrected query returned hasRightDualOfEquivalence, whose equivalence hypothesis does not describe etale-to-proetale comparison. LeanFinder's two phrasings found general condensed sheaf/free sheaf results and the algebraic Picard group, not this root-normalized signed comparison. LeanSearch returned ordinary categorical pullback comparisons, sheaf module pullback and its adjunction, and a module-dual contraction identity. The grep had a single incidental English-language occurrence in Partition/GenFun. None states the item. The historical search entries are preserved, including the older unavailable service result.

## Blueprint and duplicate search

Ran blueprint_refs.py ancestor on the item and whole-blueprint searches for signed twist, evaluation and Tate comparison. Read the sole signed-twist blueprint hit and the finite-coefficient comparison candidates in the DAG; searched the whole dag/nodes tree for mixed-sign, signed powers, evaluation and multiplication. The item's nearest ancestor remains lem-pur-frame-independence, via lem-pur-supported-cup-functoriality. There is no blueprint node stating this exact comparison. No new node was created, so no new/existing duplicate pairs require adjudication.

## Not duplicates

No new nodes.

## Review by Q101

I read Stacks sites-modules.tex at lemma-tensor-product-pullback (03EL), remark-pullback-internal-hom (0GMX), and example-dual (0FNY), and sites-cohomology.tex at lemma-pullback-tensor-product (07A4). The item concerns degree-zero finite lines, so the ordinary tensor and evaluation maps, not a derived-category comparison with hidden boundedness conditions, suffice. I also opened every cited node and read its statement; citations.json copies literal portions of those statements.

Step 1 uses the finite coefficient datum in def-pur-conventions, the explicit rank-one assertion in lem-asd-etale-finite-twist-pullback, the nonnegative tensor/pullback comparisons of lem-amb-finite-tate-site-descent, and the same-root, scalar-unchanged assertion of lem-amb-finite-root-site-comparison. The projection-induced theta and sigma are actually defined by def-pur-frame-class. The elementary annihilation check uses ell in the ideal (varpi_E), so ell^n lies in (varpi_E^n). The assumption ell != p ensures the root sheaf is locally free on every k-scheme; no finite-type or Noetherian condition is smuggled in.

Step 2 uses the actual geometric comparison-site inclusion of def-weil-pbc-site-comparison-morphism. Its inverse image has an isomorphic constant coefficient ring. The statement of lem-pur-signed-line-derived-base-change explicitly supplies the unique evaluation-normalized extension and its dual-basis formula. I also read lem-pur-ringed-site-finite-free-dual-pullback: it supplies the evaluation transpose delta, its invertibility, and its formula on dual bases. The isomorphism (t^{-1})^vee delta has the right direction: a functional on the pulled etale line is precomposed with t^{-1} to become a functional on the pro-etale line. This addresses existence and uniqueness before any local equality calculation.

Step 3 cites lem-pc-sheaf-modules-tensor-closed only for the actual associator, symmetry, unit and tensor/Hom structures that its statement gives; it is not being used for Tate descent. The normalized generator formula in lem-pur-independent-inverse-image-tensor-comparison states precisely that inverse image takes pure tensors to pure tensors. The remaining assertion is written out on a single basis: positive/positive concatenation, negative/negative evaluation on the positive total basis, opposite-sign cancellation with either positive or negative excess, exact cancellation, and zero/unit cases. Each sheaf morphism is determined by that local basis; sheaf uniqueness glues equalities. Under e -> ue the signed exponent is u^a (including inverse powers), so the two products both acquire u^(r+s). This is a local two-line tensor calculation per sign case, not a concealed general comparison theorem or a newly packaged clause of the item.

Step 4 uses only the positive scheme-pullback square supplied by finite-tate-site-descent, the natural comparison isomorphism and identity/composition laws actually stated in comparison-pullback, and the etale evaluation and pullback laws explicitly stated by etale-finite-twist-pullback. The finite-free-dual-pullback statement gives the precise transpose map used for the negative pullbacks. The module-pullback-tensor statement is bifunctorial, as needed to pull back evaluations. I wrote the two negative routes on a pulled local dual basis: both are the unique functional taking value 1 on the common positive image f'_d. Naturality of the canonical comparison is applied to the basis map from the coefficient unit; all coefficient functors retain that unit. Identity and composition follow by the same uniqueness, using the cited positive identities/compositions. This is not an unproved assertion that compatibility simply transports.

Step 5 substitutes the exact degree-one formula into the same-root tensor map and then the literal sigma definition. No cohomological identification is substituted for equality of these sheaf maps. Thus the Kummer coefficient normalization used by the ancestor is retained.

Small cases checked explicitly: r=0 or s=0; r=s=-1; (r,s)=(2,-1), (1,-2), (1,-1), and their reversed orders; d=1; identity and two successive scheme maps; empty schemes; ell=2; n=1 and ramified coefficient rings with n not divisible by the ramification index. A change of basis by a unit causes inverse powers for duals, not the positive powers (an easy possible sign/inverse error). These are unshifted sheaf lines, so no cohomological Koszul sign enters the multiplication check. Arbitrary X and v remain allowed.

I checked delivery-errors B through E against these files. There are no new statement-only nodes, duplicate nodes, new source tags, or claims of Mathlib matches. No statement correction or route departure was necessary. Each cited input is a statement, never a construction hidden in another node's proof, and the parent supported-cup node is not cited. Each step is under 2000 characters. Generic off-unit sheaf-duality and finite-root comparisons are declared in split_report.tool_uses for the maintainer's judgment; they do not replace a geometric step of the unit. No top-level maintainer tool_uses field was written.

## Unfinished

None in this one-level stage-1 split. Existing dependency nodes remain independent tasks; no Lean proof is claimed.
