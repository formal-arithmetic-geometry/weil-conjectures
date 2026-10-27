# Worker report

Group Q05; item lem-sfb-knudsen-pointed-forgetful-universal-curve; 2026-10-22. Stage 1 only, direct delivery. Files below are under dag/nodes/sec-six-functors-basics/ in this sandbox.

## Files written

- lem-sfb-knudsen-pointed-forgetful-universal-curve.json: statement split into seven steps; no Mathlib match; statement unchanged.
- lem-sfb-log-canonical-deletion-algebra.json: new statement, unsplit; no Mathlib match. Cohomology, section algebra and evaluation for a logarithmic curve with at most one degree-zero component.
- lem-sfb-section-ideal-proj-expansion.json: new statement, unsplit; no Mathlib match. Explicit symmetric-Proj expansion of the dual section ideal.
- lem-sfb-elementary-contraction-evaluation.json: new statement, unsplit; no Mathlib match. Pushforward calculation and invertible quotient, with its necessary divisor twist.
- citations.json: one literal statement quotation for every step/node citation.

The complete executed search outputs are retained in search-results.json and searches.jsonl. Each delivered node contains the corresponding actual queries, outputs and verdicts. Searches for a possible fourth, generic fibre-isomorphism node were performed, but that node was not created: the existing lem-sfb-universal-isomorphism-open is stronger and supplies it.

## Attachments

None. Searching WeilConjectures/ for the blueprint tag, Knudsen, universal/stable pointed curves and the contraction/section-ideal notions found no declaration proving this item or any new lemma. Searches with broad stabiliz* terms returned spectral-sequence, group-stabilizer and module-stabilization declarations, not stable curves. Sheaf/ has the stable-curve definition and sorried generic-extension material, which are not finished proofs of this item. Mathlib's Flat.isIso_of_surjective_of_mono (Morphisms/FlatMono.lean, line 25) requires flatness and monicity of the comparison itself; neither follows by a one-line specialization from structural flatness. It is not a Mathlib match for the geometric-fibre criterion. The already existing DAG theorem is used instead.

## Literature wanted

WANTED: literature/knudsen-projectivity-stable-curves-II-1983.pdf, Section 2, Proposition 2.1, Definition 2.3, Theorem 2.4, Lemma 2.5 and Corollary 2.6, printed pp.174--179, for lem-sfb-knudsen-pointed-forgetful-universal-curve.

WANTED: literature/knudsen-projectivity-stable-curves-II-1983.pdf, Section 1, Theorem 1.8, Corollaries 1.9 and 1.11, and Proposition 2.1, for lem-sfb-log-canonical-deletion-algebra.

WANTED: literature/knudsen-projectivity-stable-curves-II-1983.pdf, Lemma 2.2, Definition 2.3 and Theorem 2.4, for lem-sfb-section-ideal-proj-expansion.

WANTED: Knudsen, A closer look at the stacks of stable pointed curves, arXiv:1106.1588 v2, Main Lemma and Sections 3--5, for lem-sfb-section-ideal-proj-expansion.

WANTED: literature/knudsen-projectivity-stable-curves-II-1983.pdf, Lemma 2.5 and Corollary 1.5/Lemma 1.6, for lem-sfb-elementary-contraction-evaluation.

The primary author's Brown scan (https://www.dam.brown.edu/people/mumford/alg_geom/papers/1976b--DetDiv%2BKnudsenSequel-GT.pdf), including indexed printed pages 174, 177--179, and https://arxiv.org/pdf/1106.1588 were consulted online. No literature was downloaded into the repository or sandbox. Because the principal local PDF is absent, proof_origin.by is agent. The Stacks source used for the comparison was read locally: Tag 05XD, spaces-more-morphisms.tex, lemma-where-isomorphism, lines 11792ff. Tag 0G0Q in equiv.tex assumes a Noetherian base and was deliberately not substituted for the arbitrary-base theorem.

## Corrections and route

No statement dispute and no change to the imported item statement. This is a prerequisite of the stable pointed compactification in the unit sk-thm-sf-ctf-stability, hence follows that route; it does not replace the alteration route. The three new nodes are algebraic construction/calculation inputs, not copies of the universal-curve equivalence. Their statements do not assert the groupoid equivalence or representability. The root performs the degree count, checks stability of the inserted components, constructs the comparison map, proves it is an isomorphism, and identifies objects and arrows in the 2-fibre product.

I corrected a possible omitted twist before delivery: Lemma 2.5 gives q_*O_Y(t) = K tensor O_X(-D), not K itself. Accordingly the projective quotient is q^*K onto O_Y(t) tensor q^*O_X(D). I also replaced an unnecessary inline computation of the disjoint-section cokernel with the existing arbitrary-base isomorphism-open theorem applied to the expansion projection. No generic fibre-isomorphism node is added.

Off-unit tools are declared in split_report.tool_uses: projective-bundle properness, proper base change, semistable marked base change and the projective-bundle invertible-quotient universal property. They provide general scheme tools and do not change the unit's mathematical route. In particular the H-projective base-change node was not used for the project's different projectivity convention.

## Not duplicates

lem-sfb-log-canonical-deletion-algebra vs lem-sfb-nodal-log-canonical-reconstruction: the latter assumes a locally Noetherian base and H-projectivity and reconstructs an already ample positive-degree curve; the new statement is over arbitrary bases for proper families and gives cohomology/base change, generation and evaluation contraction when a component has degree zero.

lem-sfb-log-canonical-deletion-algebra vs lem-sfb-nodal-log-dualizing-pullback: the existing node is a DVR comparison of logarithmic dualizing modules under a birational morphism, not the arbitrary-base section algebra with a degree-zero component.

lem-sfb-log-canonical-deletion-algebra vs lem-sfb-semistable-log-pluricanonical-lattices: the existing statement is a DVR lattice comparison, not the construction of the relative contraction over any base.

lem-sfb-section-ideal-proj-expansion vs lem-trf-valuation-symmetric-nodal-blowup: the latter is a valuation-base local nodal blowup, not the symmetric-Proj module formed from an arbitrary section ideal and all marking divisors, with canonical labelled lifts and arbitrary base change.

lem-sfb-elementary-contraction-evaluation vs lem-trf-valuation-stable-blowdown-uniqueness: the existing node concerns sequences of exceptional pushout contractions over an algebraically closed field relative to a reference map; it does not compute these sheaf direct images or the evaluation quotient over an arbitrary base.

All new nodes vs lem-sfb-knudsen-pointed-forgetful-universal-curve: the new nodes concern explicit section algebras, a specified module and a direct-image formula. None asserts representability of a moduli fibre product or the equivalence of contraction and stabilization. Those arguments remain in the split item. Whole-DAG keyword/source searches and whole-blueprint searches (Knudsen, pointed curve, log canonical, pluricanonical, section ideal, section algebra, dual ideal, contraction evaluation, direct image contraction, stabilization) found no exact existing blueprint node. Blueprint ancestor returns null; all inherited via chains and places are retained and extended accordingly.

## Review by Q05

I read delivery-errors.md B through E in full and checked each new statement and each proof step against its input statements. I read the item in Knudsen Section 2, especially Proposition 2.1 and Lemma 2.5/Corollary 2.6. For the logarithmic algebra I checked the generation and direct-image ingredients from Section 1 and Proposition 2.1. For the expansion I read Definition 2.3/Theorem 2.4 and the 2012 paper's Main Lemma, matrix-factorization calculation and Section 5 flatness argument; the latter resolves the subtle nodal section ideal, where merely calling the ideal invertible would be false. For the evaluation node I checked the multiplication diagram in Lemma 2.5 and the evaluation quotient, with the negative D twist explicitly preserved.

Step 1 cites the actual stable-curve definition, not a definition of moduli alone. The projective-bundle properness theorem supplies properness in the right convention, proper base change preserves it, and the marked base-change theorem explicitly supplies the underlying flat finitely presented nodal curve and smooth marking locus. Stability and genus are read on the identical Omega-fibre for the composite geometric point, so there is no unproved field-extension comparison. Positive logarithmic degrees let the new algebra lemma supply projectivity, including on non-quasi-compact bases; no globally fixed projective space is presumed.

Step 2 uses the new algebra node's displayed component degree formula and its contraction conclusion. I checked the exceptional genus-one case: losing the sole special point forces that component to have no attaching branch and hence to be the entire connected genus-one curve, excluded by g>=2. Only the component containing the last section can reach degree zero, so the at-most-one hypothesis holds. The moduli definition is cited for ordered arrows and the category, not for a contraction theorem.

Step 3 uses precisely the proper/flat/finitely-presented and fibre-description clauses of the expansion node. It separately checks the three special points on either new P1 and preserves the old components' counts; stability is not inferred from an unrelated definition node. The algebra lemma's positive-degree case then gives projectivity. Step 4 uses the expansion's actual projection and the contraction algebra's stated uniqueness among fibrewise contractions to a stable family; both old markings and the image of the last marking are retained.

Step 5 uses the evaluation node's actual canonical invertible quotient, its fibrewise description, and its isomorphism/base-change naturality. The existing projective-bundle quotient theorem really concerns Hom into arbitrary symmetric Proj, not just full faithfulness of Yoneda or a chosen projective-space presentation. Its classification creates the comparison map. The existing universal-isomorphism-open statement has exactly the required hypotheses: proper flat finitely presented source and proper target imply all its listed structural assumptions. Every geometric point factors through its open, so that open is all of T, even over a nonreduced base. This avoids inferring a global isomorphism merely from an unsupported fibre argument. Naturality under automorphisms of contraction diagrams then proves fh=f and h=1, supplying the arrow part of representability rather than just a bijection of isomorphism classes.

Step 6 is the elementary unpacking of the 2-fibre-product definition using the comparisons already proved in steps 4 and 5. The isomorphism alpha is part of each object; it is never discarded modulo automorphisms of the old curve. The map on objects and its reverse are written explicitly, and naturality plus uniqueness provides the map on arrows. Sections of X_U are identified with T-maps U->X by the fibre-product universal property. Step 7 uses the expansion node's fibre description plus the same isomorphism-open theorem; it proves the assertion over nonreduced bases as well as on geometric points.

Small cases checked: r=0 (empty D, including an unmarked rational bridge after deletion); no exceptional component; a smooth extra point distinct from all markings; a collision with precisely one old marking; a node including a self-node (two normalization branches remain distinct attachment points); rational tails and bridges each carrying the new marking; elliptic tails; g=2; empty base; and arbitrary/nonreduced base change. In the smooth disjoint identity case K=O(D+Delta), so K(-D)=O(Delta), which checks the twist in the evaluation statement. On a contracted component, O_Y(t) has degree one and q^*O_X(D) has degree zero, consistent with the complete degree-one linear system in the comparison.

Every cited node was opened and its statement read; citations.json records the full literal statements so all hypotheses are auditable. No new node contains a proof or proof sketch; their proof and proof_deps lists are empty. Non-elementary construction and comparison inputs have nodes. No step exceeds 2000 characters. All delivered JSON uses ordinary single-escaped TeX and includes the inherited chapter, unit and blueprint ancestry. No SGA source is used. No Lean, compiler, Lake, repository writes, launcher edits, or additional agents were used.

## Unfinished work

No unfinished part of this one-level split. The three new statement-only nodes are intentionally left unsplit for subsequent work. Dry-run and push results will be recorded by the delivery tool.


## Repair of landing return L (2026-10-22)

The landing refused the previously reader-approved delivery because the statement of def-sfb-stable-pointed-moduli-groupoids had changed. I began with the required dry run of the retained sandbox. It exited with a citation failure exactly at steps 2 and 6: their full-statement quotations were from the earlier definition. I compared the retained item with the current repository item: apart from its split proof, dependencies, proof origin and split status, the item's existing fields agree. The item statement is unchanged. The delivery tool rebases this repair in its temporary worktree on the current server DAG.

I read the current moduli definition in full and compared it to the two retained quotations. It still defines the same ordered stable families, geometric arithmetic genus, individual-label-preserving arrows, cartesian pullbacks, 2-fibre products and representation by a discrete functor of points. It now explicitly spells out arrows over a base morphism, their composition via canonical fibre-product associativity, and the equation for arrows of a 2-fibre product. Its expanded level-cohomology, inverse-image, coarse-space and stack definitions are not invoked anywhere in this item or the evaluation lemma, and no level structure is assumed or constructed here.

In step 2 I added the action on an arrow over an arbitrary base map: apply contraction to the labelled pullback isomorphism and then its canonical base-change comparison. The contraction input already supplies naturality and uniqueness, which ensure compatibility with composition and its fibre-product associativity. In step 6 I used the definition's direction explicitly: phi goes from X_U to F_r(Y), and alpha is its inverse. The new arrow equation F_r(h) phi = phi-prime is precisely alpha-prime F_r(h) = alpha; it makes the section alpha(qt) invariant. The comparisons from steps 4 and 5 give the unique arrow between objects with the same section, including over a nonreduced base. This proves the equivalence to the discrete section groupoid in the current definition, with phi and all labels retained. I replaced both obsolete quotations by the current literal statement. The evaluation node also uses this definition in its statement; its ordered families and genus assumptions continue to have exactly the same meaning.

I re-read every other external proof citation: stable pointed curves, projective-bundle properness, proper base change, marked semistable base change, projective-bundle quotient geometry, the universal-isomorphism open and fibre products. Every retained quotation is still verbatim in the current statement; no other cited statement changed relative to these full-statement records. The construction, direct-image and comparison inputs still provide the hypotheses checked in the original Review by Q05 above. I retained the three new statement-only nodes and their recorded searches and source review. No mathematical statement or search question changed, so no replacement searches or extra nodes were needed. The smooth disjoint case, collision, nodal bridge, r=0 and automorphisms of the old family are unaffected; the explicit arrow equation additionally checks that one never quotients away the chosen comparison with the old family. Both repaired steps remain below 2000 characters.
