# Stage-1 delivery: lem-sfb-kummer-supported-nerve-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-kummer-supported-nerve-descent.json: statement, split in seven steps; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for each of the nineteen step citations.
- searches.jsonl: actual msearch results, retained; prepare.py is sandbox-only preparation code.

No new nodes and no Mathlib leaves. No Lean was written or compiled. No repository or launcher file was changed.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and combinations of Kummer, supported and nerve. The KummerCover and GaloisEvaluation files concern punctured root covers and Galois actions, and do not state the supported coherent all-continuous comparison of this item. The exact tag search found no declaration.

## Literature wanted

WANTED: an exact all-continuous reference for the root-tower supported comparison and its coherent augmented descent, including norm-topological incomplete Omega, for lem-sfb-kummer-supported-nerve-descent. The blueprint main-20261015 direct-images.proof.md paragraph (3) asserts open-image finiteness but does not supply this calculation. The assembly proof is explicitly agent-written and uses the existing geometric statement nodes as inputs, not an assertion that Stacks proves the coefficient-sensitive root calculation.

## Statement dispute and correction

STATEMENT-DISPUTED: the supplied boundary identification was not required to be G-equivariant, although the conclusion identifies the first action face with the specified representation action. This is false for a merely underlying identification. For example take p=3, ell=5, E=Q_5, k an algebraic closure of F_3, B=U=A^1_k, t_1=t, I_i={1}, I_o empty, and the usual full prime-to-3 root tower. Take constant rank-one L and N with trivial deck-equivariant coefficient action. Give the one-dimensional vector space M the nontrivial quadratic character of G via its Z_2 factor modulo 2. The underlying boundary module of N is isomorphic to p_S^*M_E, so the imported hypotheses hold. The geometric first face on the constant section 1 is 1, while the proposed bar face for an increment with character -1 is -1. The specified restriction comparison therefore cannot intertwine them. I changed exactly “Specify i^*N isomorphic to p_S^*M_E” to “Specify a G-equivariant identification ...”. This expresses the source's intended boundary monodromy and does not hide an extra hypothesis in a proof step. No target statement was changed.

## Other issues found

The item was unsplit, with no sandbox copy or report. I retained its existing searches and all inherited metadata. The item has blueprint.from.node=null because its inherited created.item chain ends without an imported blueprint node; tools/blueprint_refs.py ancestor prints None. I retained that ancestry and supplied the exact main-20261015 paragraph in from.place, instead of inventing a blueprint id. Whole-blueprint searches for support, closed cover, Mayer.Vietoris and Kummer found no identical imported item. The current unit record is the inherited sk-thm-sf-ctf-stability sketch; this item is below its open-direct-image clause and is not the unit's key statement, so its realized fields were not edited.

The earlier temptation to recompute the closed union would duplicate the existing reviewed lem-sfb-root-tower-inner-support. I opened its statement and proof: it already supplies all profinite P, the actual closed-unit equality, the union of inner branches, and full-family naturality. I cite it, rather than introducing another node for that same fact. The remaining work here is all nerve operators, coherent descent and the global slice unit.

## Mathlib searches and duplicate checks

All new searches were run through msearch.py and their actual results read. LeanFinder returned ordinary monoid classifying-space resolutions, standardComplex and ordinary Cech/nerve constructions. LeanSearch returned abstract derived adjunction units and one sectionwise module unit formula. Loogle with "Sheaf", "Kummer" returned zero hits; the Kummer/tame plus support/nerve/bar Mathlib grep returned zero hits. A second LeanFinder phrasing on totalization and augmented localization units again returned ordinary simplicial/Cech constructions. These do not give the all-continuous coefficient geometric comparison under this item's hypotheses. The imported search records remain unmodified; the new ones are appended.

## Not duplicates

No new nodes. lem-sfb-root-tower-inner-support is used for the individual supported terms and its actual-unit equation. lem-sfb-cech-localization-unit-totalization supplies the general formal descent of that unit. Neither is recreated or offered as a new proof of the whole item. lem-sfb-kummer-source-coherent-descent is a different source-only chart-existence and descent statement, and was not needed for our supplied chart. The field-specific lem-sfb-galois-limit-nerve-faces was not cited for an arbitrary scheme torsor; the face formulas are explicitly substituted from the assumed torsor isomorphism.

## Review by N5

I read AGENTS.md, the worker role, the stage-1 brief and stage document, GOAL.md, SETUP's three-level rule, the chapter and unit records, tools/README.md and both copies of delivery-errors B--E. For the mathematical source I read main-20261015 sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3). It motivates the open-image route but supplies no proof of this specific assertion. I also read Stacks proetale.tex Tag 09AA (lemma-closed-immersion), Tag 09BM (lemma-closed-immersion-complement-retrocompact-exact), Tag 09AH (lemma-ses-associated-to-open), and sites-cohomology.tex Tag 03FC (lemma-injective-module-trivial-cech). These justify the nature of the generic exact localization and injective Cech inputs, not the all-continuous root calculation. No prohibited SGA route is used.

Step 1 uses the lisse definition's actual finite-free slice models and the strong monoidal coefficient pullback, followed by the exact statements of boundary-acyclicity and root-tower-inner-support. I checked both complete statements against U, S, T, the partition, N, and M_F. Their coefficient fields and topology conventions agree; the support theorem does not need a torsor or chart-existence theorem. Ordinary scalar extension is locally finite free, and a basis of finite-dimensional M identifies continuous functions with a finite product of the coefficient ring. Equivariance of that boundary identification is the correction explained above. The support theorem's displayed sigma_P eta = alpha_P is exactly the equation this step uses.

Step 2 uses the two inputs' parameter and whole-family clauses, not just a pointwise equivariance assertion. I wrote the cumulative vertices and each deletion/repetition formula. The first face moves x to xg_1 and transports the module by the supplied equivariant identification; its square is over Q=G. The remaining faces are continuous multiplication/deletion/insertion maps of G-powers. Thus the cited naturalities say precisely what is required to identify the bar operators. All maps are those of the original augmented Cech object, so the operator identities are preserved.

Step 3 uses weakly-etale localization clause (1) only. Its statement explicitly identifies the sites and coverings; its constant-ring clause is not used for C_F. The ringed-open-closed statement supplies exact closed direct image and the unit of the indicated inverse/direct adjunction. The Cech-localization-unit-totalization statement has five ringed topoi, exact inverse images, an exact closed adjunction, a covering sheaf epimorphism, and degree-zero N. I checked f=b, g=a, t=s, N=L_F, C_n=K_n, and the assumed torsor is a pro-etale cover. The theorem explicitly identifies the arrow as the totalized actual unit and preserves augmentation. Derived-composition-adjunction-normalization explicitly says the units are the composite units, which is the normalization used for a f_n.

Step 4 uses the nonnegative-derived-totalization statement's compatible replacements retaining operators and its naturality for augmented diagrams. The derived-Cech-image-totalization statement explicitly allows exact inverse image through the finite diagonals. I checked that no negative resolution or Cech degree is introduced: all inputs are degree-zero sheaves and right derived images, so a fixed total degree contains finitely many pairs, or triples after a further replacement. The cone-column argument then proves invariance of these totals under the termwise isomorphisms. These are coherent resolved objects throughout; no unbounded product-total claim is inferred. Step 5 is only composition of the commuting diagram and requires no additional lemma.

Step 6 takes precisely the naturality clauses already used in steps 1--4. It does not require scalar extension to commute with a derived image. I checked the trivial outer group (a identity), one inner branch, zero rank, empty U and empty S. When only S is empty, both comparisons are on the empty topos after s^*, so the resulting zero diagrams have the unique isomorphism. The argument treats both fields separately on the same root choices. Each non-elementary proof step is shorter than 2000 characters; no long step conceals a new lemma.

Step 7 addresses a genuine limitation of the formal Cech theorem: its slice clause only restricts the original arrow, and does not itself construct a sliced arbitrary adjunction. I opened the full statement of lem-sbc-ringed-topos-sheaf-slice-derived-comparison. It supplies ordinary and derived slice comparisons for any target sheaf, represents the image comparison on K-injectives, and asserts that it is the adjunction mate of the inverse-image comparison, with a counit equation. I checked the sheaf is the pro-etale object U over Y and that the source slices are precisely W, V and Z with pulled-back rings. The unit equation follows from that mate assertion by taking its adjunct: both are the identity. Applying this to h_0 and b_0, then the direct-image comparison for j_0, gives the actual global unit restricted to U. Closed exactness allows h_* rather than a newly derived support functor. This is the arbitrary-ringed-slice tool needed here; the finite-type bounded-coefficient open-square lemma would not apply and is not cited.

I checked that none of the cited nodes depends back on this item, and read each statement rather than borrowing objects from its proof. The off-unit inputs are declared as generic tools in split_report, with their precise roles. No new statement-only nodes were required, so B1--B8 for new nodes are vacuous. The only mathematical correction is the explicit missing equivariance hypothesis; all remaining hypotheses and conclusions are retained.

## Unfinished work

None in this one-level split. The unresolved geometric facts remain the existing cited DAG nodes, not unnamed claims. Required dry-run and push results are reported by the delivery command.

Dry-run repair: the first invocation stopped before server preflight because the short quotation “The functors j_! and i_* are exact” normalized to fewer than forty characters. I replaced both entries by the complete ringed-open-closed statement, which also exposes the unit and all localization hypotheses. No mathematical change resulted. I additionally read sites-modules.tex Tag 04IF, lemma-localize-morphism-ringed-topoi, lines 2705ff: it explicitly gives the ringed slice square and restriction/direct-image identity used by the generic derived slice input.
