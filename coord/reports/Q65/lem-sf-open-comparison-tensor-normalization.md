# Q65: lem-sf-open-comparison-tensor-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-open-comparison-tensor-normalization.json`: statement, split; no Mathlib match. The statement is unchanged. Added the ordinary tensor-comparison statement dependency, six proof steps, their exact proof-dependency union, blueprint provenance, and declared generic tool uses.
- No new nodes; zero new Mathlib leaves.
- `citations.json`: a verbatim statement quotation for every step/node citation. The quoted statements were read in the shared DAG, including their hypotheses.
- `searches.jsonl`: actual msearch.py queries and returned search digests. The item's earlier Q04 searches were preserved; Q65 searches were appended to the node from this log.

## Attachments

None for the item. Searched the exact blueprint tag and the open/comparison/tensor concepts under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`, including the etale open-immersion lower-shriek files, pro-etale comparison files, and derived projection-comparison files. There is no declaration giving this precise equality for the ordinary constant-A sheaf maps. In particular `AlgebraicGeometry.ProEtale.isMonoidal_comparisonUpperStarCompUpperStarIso_hom` in `WeilConjectures/SixFunctors/ProEtale/Comparison/Monoidal.lean:123` concerns only the pullback comparison, while the derived direct-image projection comparison concerns different maps. Neither is an attachment for this item. The upstream master source was treated only as reference material.

## WANTED

None. All mathematical sources used are already in literature.

## Problems found and corrected

The seed was statement-only. Its statement is well typed, and I found no statement dispute. Stacks 09AF proves extension comparison by the common right adjoint; it does not state this tensor equality verbatim. Accordingly the expanded proof is explicitly marked agent-written. I retained the source's adjunction route and expanded the actual-map calculation rather than claiming that an isomorphism between the two functors proves equality of their tensor maps.

The pullback-comparison node states naturality and composition compatibility, not tensor coherence. Step 2 therefore proves the needed tensor square from naturality on underlying set sheaves, finite products, and the existing pure-tensor normalization; it does not quote a nonexistent tensor clause from that node. This is a short formal argument, not a new lemma node. Generalized pure tensors, rather than arbitrary presumed sectionwise tensor presentations, are used to respect sheafification.

The proof uses neither conservativity of geometric points on the pro-etale site nor faithfulness of open restriction on arbitrary sheaves. It uses the actual open Hom bijection on the fixed extended source. Neither projection map needs to be known invertible. All coefficients remain ordinary constant finite commutative rings; no condensed, completed, rational, derived, finite-type, Noetherian, or characteristic hypotheses enter this item.

## Unfinished work

None in the one-level split. Existing cited nodes retain their own current states; no other node, unit, source, or maintainer-owned field was changed.

## Not duplicates

No new nodes were created. Whole-DAG key-word/tag searches and blueprint_refs.py searches for `open comparison tensor normalization`, `unit normalization`, `open-extension`, `monoidal`, `tensor-product-pullback`, and `projection formula` found no imported blueprint node stating this comparison equality. The item's nearest blueprint ancestor is `lem-weil-finite-compact-projection-formula`; its final pro-etale paragraph is the recorded provenance. Existing tensor and open-adjunction nodes were reused.

## Review by Q65

I read the unit `sk-thm-sf-pf-finite`, its chapter record, the current main-20261015 proof of `lem-weil-finite-compact-projection-formula`, and Stacks `proetale.tex`, Tag 09AF, label `lemma-jshriek-comparison` (lines 5076 onward). That lemma is for an etale morphism and abelian sheaves, and its proof identifies the two extensions by their common right adjoint. Here the morphism is open, and the ordinary module version is supplied by the cited module adjunctions, so no assertion about arbitrary module objects or other coefficient models is being imported. I also read `sites-modules.tex`, Tag 03DI (`lemma-extension-by-zero`), Tag 03EK (`section-tensor-product`, including its universal bilinear-pairing characterization), and Tag 03EL (`lemma-tensor-product-pullback`). The tensor refinement is my explicit calculation from these sources and the existing normalized comparison statements.

In step 1 I checked that `lem-weil-pbc-extension-by-zero-adjunction` actually gives the etale module Hom bijection, that `lem-weil-proetale-weakly-etale-localization` gives both the open-site identification and the constant-ring identification, and that `lem-pur-site-restriction-module-adjunction-exact` gives the pro-etale module Hom bijection after that identification. The open immersion is among the latter localization lemma's stated examples. The equation in `lem-sf-open-comparison-unit-normalization` is exactly the equation used at N. It converts Psi to the pro-etale transpose after precomposition by c_N inverse, proving injectivity without assuming an inverse for the restriction functor. This step uses the statements of the nodes, not their proofs.

In step 2 I checked the arbitrary-ringed-topos hypotheses in `lem-weil-pbc-ringed-topoi-module-pullback-tensor`; all sites are the project's fixed small representatives, and all coefficient ring maps are the canonical constant-ring identifications. Clause (1) of `lem-sf-comparison-pullback-exact` identifies the comparison module inverse image with algebraic inverse image; its exactness and derived clauses are not used. The statement of `lem-weil-pbc-algebraic-inverse-image-tensor-comparison` explicitly normalizes the forward map on generalized pure tensors, and `def-weil-pbc-ringed-tensor-section-calculus` explicitly says pure pairings determine linear maps. The comparison a is the canonical underlying sheaf inverse-image comparison in `lem-weil-pbc-comparison-pullback`. Naturality with product projections and then with the universal pure pairing proves its tensor square. This verifies the extra square instead of attributing it to the pullback-comparison statement. The argument applies to underlying set sheaves first and then to their transported A-module structures. It is an elementary consequence of those cited normalized maps, so making it a fresh node would duplicate a two-line universal-pairing calculation.

In step 3 I checked the directions and types: N=F tensor rB, L has source C_X eN, and Psi(L) has target s(d C_UF tensor C_XB). The etale adjunction says precisely rho^e r(kappa^e) eta_N = eta_F tensor identity. Naturality of a with kappa^e moves that map inside C_U. Applying the explicitly proved square (*) and naturality of t and rho leaves the factor s(c_F) a_eF C_U(eta_F), exactly the unit-normalization node's left-hand side. Thus the step reaches (eta^d tensor a_B) t^U with the right orientation, using no additional projection-formula theorem.

In step 4 I checked the same normalization at N, not just at F. Naturality of eta^d with q moves d(q) past the unit. The stated definition of kappa^d then gives rho^d s(kappa^d) eta = eta tensor identity. This is the module adjunction of the cited localized-site node, so the same ordinary tensor target as step 3 is obtained. This step does not equate maps merely because their sources and targets are isomorphic.

Step 5 is just cancellation of the invertible rho map followed by injectivity already proved in step 1. Step 6 verifies the extra naturality clause: the unit squares give equal transposes for each kappa naturality square, the Hom bijections make those squares equal, and the cited comparison/tensor nodes explicitly supply naturality of a, c, and t. Thus all non-elementary ingredients are cited and no separate unproved compatibility is hidden.

I tested the boundary cases: j the identity gives the natural tensor comparison on both sides; U empty gives maps from the zero module sheaf; F=0 or B=0 gives the zero map; the zero finite ring also has only the zero module sheaf. No stalk, freeness, nonzero coefficient, or nonempty-open argument is used. The displayed formulas type-check as compositions of sheaf maps in each case. No Lean compiler was invoked.

I checked delivery-errors B through E against the files: no new statement-only nodes, duplicate nodes, Mathlib leaves, or disguised clauses of the item were introduced; the statement is unchanged and introduces its objects; all cited statements were opened and copied verbatim into citations.json; the proof-dependency list is the exact union of step uses; and no SGA route is used. Every step is below 2000 characters (the longest is step 2 at 1470), and I checked that the tensor square is the explicit short naturality/pure-pairing calculation, not an omitted comparison lemma. Generic off-unit tools are individually justified in split_report.tool_uses; no unit or chapter route was replaced. The new Mathlib searches returned open-immersion structure-sheaf formulas, unrelated etale-algebra facts, and generic adjunction/monoidal formulas. I read the relevant generic `Adjunction.homEquiv` definition and the monoidal-adjunction formulas: these do not assert this site/open-extension equality, so the item remains split rather than a Mathlib leaf.
