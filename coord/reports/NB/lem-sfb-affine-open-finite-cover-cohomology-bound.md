## Worker report

Group NB, stage 1, item lem-sfb-affine-open-finite-cover-cohomology-bound, 2026-10-24. Direct delivery with worker self-review as authorized by the brief.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-open-finite-cover-cohomology-bound.json: statement, unchanged; status split; five proof steps following the first proof of Stacks Tag 01XI; Mathlib verdict no exact match.
- citations.json: one verbatim statement quote for each of the eleven step/node citation pairs.
- report.md: this report and signed mathematical review.

No new nodes and no new Mathlib leaves. The sandbox's existing searches.jsonl is retained and extended by the actual searches made in this attempt. write_split.py is a sandbox-only editing aid, not a project delivery file.

## Attachments

None. The previous proposed attachment was rejected: the proposed declarations did not exist, and no attachment established all clauses including the empty cover. I did not repeat that claim. I searched the live WeilConjectures source by the item tag and finite-affine-cover/cohomology concepts. The actual FiniteAffineCoverRestrictionBound theorem concerns etale sheaves, explicit local acyclicity, and a nonempty cover, so it is not this item; the topological MayerVietorisVanishing theorem gives a general abelian-sheaf induction ingredient, not this module-sheaf statement. The present delivery supplies the natural-language split.

## WANTED

None. All sources used are available in literature/stacks-project/ and were read there.

## Existing material and searches

I read AGENTS.md, GOAL.md, the stage-1 worker brief, roles/worker.md, stages/1-dag.md, the three blueprint levels in SETUP.md, the chapter/unit records, and delivery-errors B--E. I read the latest blueprint chapter, the current sk-thm-sf-ctf-stability unit, and sk-thm-sf-ctf-stability-direct-images.proof.md (of det-thm-sf-ctf-stability-direct-images). The relevant place is proper/direct-image preservation in proof (3), through the inherited chain of auxiliary supported-perfect approximation lemmas. The immediate caller lem-sfb-affine-supported-class-lift uses precisely the bound for the given s-affine cover in the first paragraph of Stacks 08E3. Nothing in that upper route is changed.

I searched the whole DAG for 01XI, affine intersections, cohomology comparisons, Mayer--Vietoris, and affine vanishing. I ran blueprint_refs.py searches for affine cover, affine intersection, 01KP, 01XI, finite-cover-cohomology, and Mayer.Vietoris. The affine-cover query returns the existing Cech-comparison blueprint nodes; none states the present bound with all its hypotheses. The tag and intersection searches found no same-statement blueprint node. No new node is needed: existing generic inputs suffice. In particular lem-sc-picard-qcoh-finite-cd has a field hypothesis and only an unspecified finite bound; lem-sc-picard-affine-diagonal-intersections also assumes a field. Neither can be used to obtain the present field-free statement. The general separated-affine-open-intersection Mathlib leaf can be used after choosing an affine presentation, and is cited instead.

The five existing sandbox searches were read and reused: no affine/cohomology grep hits; no cohomology/Cech Loogle hits; LeanSearch returned quasi-coherent data and finite-cover constructions; LeanFinder returned section-vanishing/limit and Cech infrastructure. These do not state the item. A second semantic phrasing, "Right derived global sections of quasi coherent modules on a finite union of affine opens vanish by Mayer Vietoris induction", returned quasi-coherent data and section-vanishing lemmas, again no bound. A new recorded grep for IsAffineOpen/diagonal/separated names located isAffineHom_diagonal_iff and IsAffineOpen.inf, agreeing with the existing intersection leaf. All recorded queries are either inherited unchanged from the live item or actual entries of this sandbox's searches.jsonl. No failed service is described as a negative result.

## What was wrong and what changed

The statement is correct and is kept byte-for-byte. There is no statement dispute or source correction. The item previously had no proof. I supplied the first proof of 01XI as induction on the supplied cover size, avoiding any assumption that it is minimal. Stacks' printed induction begins at one; I explicitly proved the s=0 case from the empty-cover sheaf axiom and the definition of module cohomology. I also made the affine-presentation argument, preservation of quasi-coherence under restriction, and open/global cohomology comparison explicit rather than treating them as implicit identifications.

blueprint_refs.py ancestor reports None for the existing created.item chain. Its inherited blueprint.from.node is null and its from.place already identifies the precise long provenance through 08E3. I retained these existing values and filled same_as and split_report.blueprint. No new node needs an invented blueprint ancestor.

The open-restriction cohomology comparison and ringed-space Mayer--Vietoris are used as generic tools from other units: they provide exactly the local cohomology identification and exact sequence used by Stacks 01XI. The item unit supplies no replacement for those generic cohomology statements. No unit route or top-level tool_uses record was edited.

## Review by NB

I read coherent.tex, lemma-vanishing-nr-affines (01XI), including both proofs, and retained its first, Mayer--Vietoris proof. I also read coherent.tex, lemma-quasi-coherent-affine-cohomology-zero (01XB), schemes.tex, lemma-characterize-separated (01KP), modules.tex, lemma-pullback-quasi-coherent (01BG), and cohomology.tex, lemma-cohomology-of-open (01E1) and lemma-mayer-vietoris (01EB). The tag-to-label table confirms these places. The statement needs neither a field nor Noetherian or finite-type hypotheses. A supplied s-member cover is sufficient; minimality is unnecessary. There are no new-node statements to check against a separate source.

Step 1 cites def-weil-sheaf-of-modules-category for an underlying abelian sheaf and def-sc-ringed-space-module-cohomology for computing cohomology by the section complex of an injective resolution. Their statements say exactly those things. The empty-cover sheaf axiom forces the empty-open section group of every term to be zero, so its section complex and all its cohomology groups are zero. This is a direct elementary calculation, including degree zero, not an appeal to an abelian/module cohomology bridge.

Step 2 cites def-pc-scheme for an affine presentation, def-weil-proper-morphism for separated meaning closed diagonal, and def-weil-closed-immersion for the closed-subspace/surjective-structure-map criterion. For the chosen isomorphism Y to Spec A, the diagonal is inverse to a pullback projection. Its being a closed immersion follows from those definitions on the whole target. I then checked the exact statement of lem-weil-pbc-separated-affine-open-intersection: it assumes a commutative ring and a separated map to its spectrum and gives affineness for every pair of affine opens, with no field or compactness assumption. These are the hypotheses just established; it applies to the original affine ambient Y. Opens of U are opens of Y, so no mistaken claim that arbitrary quasi-separated intersections are affine is made.

Step 3 cites def-pc-module-pullback for the tensor/inverse-image formula and lem-weil-pbc-module-pullback-quasi-coherent for quasi-coherence of the pullback along any scheme map. For an open inclusion the formula reduces to restriction and tensoring over O_W with O_W. I checked that lem-pc-open-restriction-module-cohomology explicitly compares cohomology on the open scheme with ambient openModuleCohomology after forgetting global scalars, for every degree including zero and with no nonemptiness assumption. It is exactly the identification needed to apply the induction and Mayer--Vietoris in the same cohomology theory. The proof does not conflate R^p Gamma on modules with Ext cohomology of an underlying abelian sheaf.

Step 4 cites pqf-lem-affine-vanishing, whose statement covers every affine open in any scheme and every quasi-coherent module, in all positive degrees. I checked its statement dependency pqf-def-cohomology: it defines module right-derived global sections, the same notion as the item's def-sc-ringed-space-module-cohomology. For s=1 the whole U is affine and p is positive. For s>=2 the induction is simultaneous over all the item data and uses strictly smaller size s-1. Both V and V intersect W are opens of the original affine Y; their covers have exactly the supplied s-1 positions, including duplicates or empty members, and their modules are quasi-coherent by step 3. Since p>=s, both p>=s-1 and p-1>=s-1 hold. On W, p>0, so affine vanishing applies. These are the three precise vanishings used next, not an unspecified eventual bound.

Step 5 cites lem-sc-mayer-vietoris-ringed-space. I read its statement and verified that it gives the full long exact sequence for any module on a ringed space covered by two opens, including the segment with H^(p-1) on the intersection and H^p on the union. Thus it does not merely provide a Hom exactness fragment or an etale sequence with other coefficients. Here V and W cover U; step 3 supplies the open/global identifications. All outer terms are zero by step 4. Exactness at the middle says every element comes from the zero left term, so it vanishes. No unstated five-lemma or spectral-sequence argument is used.

For small cases I checked s=0 and p=0; s=1 with U affine or empty; s=2 and p=2, where the needed intersection degree is exactly one; repeated cover members; empty individual members; the zero module; and arbitrary affine bases, including the spectrum of the zero ring. Every case is covered without changing the statement. All five steps are shorter than 1000 characters, so there is no long step hiding a subsidiary lemma. The proof uses statements of cited nodes, not constructions only present in their proofs. The eleven quotes in citations.json are copied verbatim from those statements. B1--B9 impose no new-node obligations because no node was created; C1/C4 are discharged by the explicit citations and comparisons above; the induction carries the item's argument rather than moving a clause into a child node (D1/D2). There is no SGA citation.

The server checks run through srvcheck.py both passed: review_split reports PASS with zero new nodes; check_dag reports no finding introduced by the sandbox or on its nodes. The mathematical review is complete. The mandatory delivery dry run and final push follow this review.

## Unfinished work

None in this one-level stage-1 split. Existing cited unsplit statements remain existing project work; no Lean was written or compiled.
