# Q15 — lem-sfb-minimal-parabolic-flag-projection

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-minimal-parabolic-flag-projection.json`: statement item, now split in twelve steps; statement and statement dependencies unchanged. Not a Mathlib leaf.
- No new nodes and no new Mathlib leaves. The matrix and coset calculations are steps of the item; every structural input already has a node.
- `citations.json`: one checked verbatim statement quotation for every node cited in every step. `searches.jsonl` contains the searches actually run with the prescribed msearch command. The two small writing scripts are sandbox working files, not delivery files.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for minimal-parabolic, Borel-subgroup, flag-variety and root-subgroup names. No project declaration states this item. An abstract quotient group, a projectivization of a vector space, and a Grassmannian module are not these algebraic-group quotient schemes.

## Literature

WANTED: Brion–Kumar, *Frobenius Splitting Methods in Geometry and Representation Theory*, §2.1 printed pp.62–63 and §2.2.1 diagram (D), for lem-sfb-minimal-parabolic-flag-projection. The local PDF named by the item is absent. I read the [author-hosted PDF](https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf) online, especially the paragraphs defining minimal parabolics, identifying the Schubert curves, and describing the locally trivial principal bundle and flag projection. No document was downloaded or written to the repository. The proof is marked agent-origin, as required when the named source is not in local literature.

For the actual argument I read the available `literature/milne-algebraic-groups_iAG2017.pdf`: Theorem 20.33 and Corollary 20.34, pp.418–419; Theorem 21.11 and 21.19–21.24, pp.428–432; 21.89–21.91, pp.453–454; and the flag-variety discussion around Theorem 17.9, pp.353–356. The printed 20.33 omits its rank-one hypothesis and mislabels some derived groups: the existing classification node already corrects both, and only that corrected statement is used. No SGA source is used.

I also read the Stacks source `morphisms.tex`, `lemma-projective-permanence` (Tag 0C4Q), including its closed-graph proof. It supplies H-projectivity with the same finite projective-space dimension, not merely properness or projective-bundle embeddability. The affine-space, open-immersion, composition and locality facts used for smoothness are the existing nodes with the Stacks sources recorded there.

## What needed correction or clarification

The original item had no proof, but its statement is correct under the group-scheme meaning of “root coordinate” supplied by its root-parametrization node. There is no statement dispute and no change of hypotheses. Simply connectedness is retained, although the proof actually works for the existing more general reductive rank-one models.

A tempting shortcut would be to infer the requested global finite-projective-space embedding just from local projective-line charts. I did not use that inference: steps 11–12 first prove projectivity of the full flag variety using the existing Borel variety, then apply the closed-graph permanence lemma to the separated partial flag target. Also, set-theoretic Bruhat decompositions are not used to infer scheme isomorphisms: explicit sections and inverse regular maps establish those isomorphisms.

The item's existing `blueprint.from.node` is null, as confirmed by `tools/blueprint_refs.py ancestor`; its detailed place and via chain are retained. I read the current `literature/blueprint/latest/` unit and its direct-image proof. This rank-one geometry is a supporting prerequisite in the existing alteration/moduli/flag-geometry ancestry of direct-image step (3), not a replacement of that route. The chapter and unit are not key-node realization items here and were not edited.

## Searches and reuse

Whole-DAG searches for parabolics, rank-one matrix groups, flag quotients and associated projective geometry found the existing standard-Levi, rank-one classification, regular-cocharacter Borel, homogeneous quotient and projective-permanence nodes. I opened their complete statements. Whole-blueprint searches using `tools/blueprint_refs.py search` returned no parabolic or rank.one matches; “flag” found only `p-linear-triangular`, a linear invariant-flag statement, which does not state any assertion here. Therefore `same_as` remains empty.

I ran the prescribed leanfinder, loogle, grep and leansearch commands for the item, with a second semantic phrasing and a second grep restricted to AlgebraicGeometry. I read all returned hits. The semantic hits were abstract projectivization, topological bundles, Grassmannian modules and general Proj charts. Loogle's parabolic hits concern discriminants of two-by-two matrices. Both source greps returned no algebraic-group parabolic/Borel/flag-quotient development. None is an exact match or a one-line specialization giving the item. The original searches are preserved and the newly run searches appended with their actual logged results. No unavailable service was reported as an absence verdict.

## Not duplicates

No new node is proposed. In particular the rank-one quotient computation is written out with two determinant-one matrix sections; it has not been repackaged as a new node that would merely repeat a clause of the item.

## Review by Q15

I checked this split against delivery-errors B–E with both the node statements and the sources open. There are no new statement-only obligations to audit. All new mathematics in the item is either an application of a named existing theorem or an explicit elementary calculation; the following describes the hypothesis and citation checks, rather than just the mechanical results.

1. The standard-parabolic node explicitly gives **both** semidirect products, with the same radical, as scheme isomorphisms. Its Levi for a singleton is the same centralizer as in the rank-one-reflection node. That latter node explicitly asserts semisimple rank one, so I do not infer a classification hypothesis from Lie dimension alone. The algebraically closed base and reductivity follow from the item's hypotheses.
2. The classification is of the pair with its torus; no unrecorded conjugacy theorem is needed. The regular-cocharacter node describes every Borel containing that torus as a limit subgroup and gives the sign of its root weights. The standard-parabolic statement says the positive roots of this Levi Borel are the restricted positive roots. The coefficient limit calculation therefore makes the Borel upper triangular over every algebra, not just over the base field. PGL computations are fppf-local matrix computations, not an assumption that every PGL-valued point lifts globally to GL.
3. I wrote the two matrices and their inverses and checked determinant one, first columns and the upper-triangular residual factor. This works simultaneously for SL, GL and PGL and kills the additional torus factor. The homogeneous-quotient node represents the fppf right-coset sheaf; `def-sc-p1-standard` gives the actual projective-line charts. Thus the sections identify quotient schemes, not only their rational points. This is the elementary two-chart computation itself, not an appeal to a new rank-one flag theorem.
4. The standard-parabolic node says the radical is normal in the semidirect product and lies in the Borel. The written formulas move that radical to the right and identify the coset sheaves. Local matrix sections then provide the inverse torsor trivialization. This supplies actual regular sections, rather than inferring a torsor has Zariski sections from its abstract fppf property.
5. The reflection node asserts uniqueness of the nonidentity rank-one normalizer class. The matrix representative has that class, and the chosen representative differs from it by an element of T. The root-subgroup node's uniqueness applies to the explicit smooth connected normalized matrix subgroup with the same root tangent space. The remaining coordinate change is scalar, proved by multiplying polynomial degrees for an automorphism and its inverse; it is not a Frobenius or differential identification in positive characteristic.
6. This step uses steps 4–5 and has no independent theorem citation. The displayed inverse to multiplication recovers the quotient coordinate and divides by its chosen lift. In particular the inverse-image scheme, not just its geometric point set, is the product with B. The two sets of field points are then disjoint by their projective-line images. This distinction led me to remove a redundant standard-parabolic torsor citation: that node states the G-to-G/P torsor, whereas the P-to-P/B torsor was already constructed in step 4.
7. The root-parametrization statement gives exactly the conjugation identity over all commutative algebras. The normalizer statement explains why the residual factor lies in T and then B. I checked the action is by alpha, rather than its inverse, with the specified left action and right cosets.
8. The standard-parabolic node explicitly supplies a finite Zariski covering with sections and the right P-torsor identity. The Borel-pair node supplies the right B quotient. The two inverse formulas therefore descend to quotient sheaves; no associated-bundle representability theorem is assumed without a node. The already represented local products glue to the existing Q.
9. The standard-parabolic quotient is proper, hence separated by `def-weil-proper-morphism`. Pulling back its diagonal along the identity coset proves that coset is a closed subscheme. The cited closed-immersion base-change node then applies to q. The fibre is identified by the fppf equality gP=P, so there is no inference from set-theoretic membership to a scheme factorization.
10. I checked each cited smoothness statement: affine space is smooth over any scheme, an open immersion is etale, etale is smooth in the cited convention, composites are smooth, and smoothness can be checked on a source open cover. These maps are the actual chart maps into H, through its open subschemes, so the locality hypotheses fit.
11. The general-Borel-flag statement gives a smooth projective scheme, transitivity on F-points and the **scheme-theoretic** stabilizer B. The homogeneous-orbit statement identifies that reduced orbit with the represented quotient. The two field/Jacobson nodes give closed-point rationality and density in every closed subset. Hence the locally closed orbit is dense and open, and its closed complement is empty. The smooth-geometrically-reduced node ensures the orbit's reduced structure agrees with the whole smooth Borel scheme. I checked all these statements explicitly; the argument does not assume an arbitrary bijective morphism is an isomorphism.
12. The H-projective permanence node has exactly the necessary triangle hypotheses and supplies an embedding in a finite projective space of the same dimension. The target's separatedness comes from its properness. Thus the conclusion agrees with `def-pc-projective-morphism`, not a weaker convention. I declare this off-unit node in `split_report.tool_uses` as a general geometry tool; the maintainer decides its approval.

Small cases checked: G=SL2, where P=G and q is the projective line over a point; a product of two SL2 factors, where the unused factor cancels from P/B; rank zero, where no alpha exists and the item has no instance; an arbitrary torus multiple of the chosen normalizer representative; characteristic two, where both displayed determinant-one sections remain valid; and nonreduced F-algebras, where the coordinate identities and subgroup equalities remain polynomial identities. For SL2 the torus character is t squared, and the action formula is t squared times a even in characteristic two, rather than the differential of that character.

The twelve steps are all under 2000 characters. I inspected them for hidden standalone non-elementary comparisons: the structural comparisons cite existing theorems, and the quotient, local-product and coordinate comparisons give explicit inverse formulas. There is no induction and no circular citation of the gallery or Schubert results that use this item. `citations.json` was checked by literal substring against every cited live statement.

## Unfinished work

None in this stage-1 split. Existing cited nodes retain their own proof obligations. No Lean was written or compiled, no agent was started, and no repository or launcher file was edited.

## Dry-run repair

The first captured server preflight rejected the TeX row separator in the displayed matrices as a doubled backslash (B4). I rewrote the same two matrices with matrix units, explicitly defined in the step, and rewrote the Weyl representative likewise. No mathematical statement or argument changed.
