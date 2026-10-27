# Q26 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-lft-group-quasicompact-open-ample.json: item, statement, split in six steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-ample-pullback-qc-immersion.json: new statement-only node, unsplit; no Mathlib match after LeanFinder (two phrasings), Loogle, LeanSearch and Mathlib grep.
- citations.json: one verbatim statement quotation for each of the 19 step/node citations.
- searches.jsonl: ten actual searches, including two semantic phrasings for the item and for the new lemma; all services responded.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and for group/quasi-projective/ample notions, and read GroupScheme/QuasiProjective.lean and AmpleFamily.lean. GrpObj.exists_isImmersion_projectiveSpace and the ample-family theorem assume the ambient group is quasi-compact. They do not state this item for arbitrary locally finite type groups or for arbitrary open subschemes. They are not attachments. The upstream closed-immersion pullback results in Modules/VeryAmple.lean do not cover open immersions either.

## WANTED

None: the sources for this split are locally present. No SGA source was used.

## Findings and corrections

The imported item is true, with its full hypotheses and all clauses unchanged. Its empty proof did not justify passing from finite-type groups to opens in a possibly non-quasi-compact group. I supplied that passage rather than treating U as a group, or applying a finite-type component theorem to H. In particular lem-sfb-group-neutral-component-translates is not cited: its finite-type ambient hypothesis is unavailable. The analogous translation argument here is written out from the lft neutral-component theorem, Jacobson closed points and translation isomorphisms.

The new input is the general Stacks 0B3E(2) theorem, not a restatement of either clause of the item. It applies to arbitrary schemes and immersions with quasi-compact source. Merely intersecting an affine section locus with an open need not leave it affine; therefore restriction of ampleness was not marked elementary or hidden in the gluing step.

The blueprint ancestry helper reports from.node=None for this auxiliary chain. I retained that live ancestry and its via chain, adding a precise place for the new restriction input. I read the current latest blueprint's six-functor stability unit and its proof, and searched all imported blueprint nodes for quasi-projectivity, ample, 0B3E and restriction of an ample module. There is no direct blueprint counterpart to the new node. This split supplies the already chosen field-effectivity auxiliary; it changes no chapter or unit route.

## Not duplicates

lem-sfb-ample-pullback-qc-immersion vs lem-trf-ample-restrict-closed-immersion: the existing lemma assumes a closed immersion; this node permits an immersion with merely quasi-compact source, including nonclosed open subschemes.

lem-sfb-ample-pullback-qc-immersion vs lem-weil-pbc-pullback-ample-invertible: the existing lemma assumes an affine morphism; a quasi-compact open immersion need not be affine. This node is the independent locally closed restriction theorem 0B3E(2).

lem-sfb-ample-pullback-qc-immersion vs lem-trf-proj-qc-open-twist-ample: the latter concerns the construction and multiplication of twists on a graded Proj; this node restricts an arbitrary supplied ample line on an arbitrary scheme and has no graded hypothesis.

The whole-DAG tag search found no existing 0B3E source node. The incidental string hit in open-restriction-kernel-module concerns ideal sheaf kernels and supplies no ampleness assertion.

## Review by Q26

I read Stacks groupoids.tex 0B7R (proposition-connected-component) and 0BF7 (lemma-algebraic-quasi-projective), varieties.tex 0BDC (lemma-ample-after-field-extension), and properties.tex 0B3E (lemma-ample-on-locally-closed), including condition (2) and its proof. I also read the Jacobson statement 0478, residue-field criterion 01TB, finite-type base change 01T4 and group separatedness 047L. The proof origin is correctly agent-written: this is an adaptation of the sources to quasi-compact opens, rather than a verbatim theorem in 0BF7.

For step 1, I opened def-weil-finite-type-morphism and def-weil-open-immersion. The former defines lft by affine charts and finite type as lft plus quasi-compact. Localizing a finitely generated algebra adds just the generator f^{-1}; principal charts within U and a finite subcover prove the clause directly. No global finite-type hypothesis on H is used.

For step 2, I read def-weil-algebraic-closure, def-pc-fibre-product, def-sc-group-scheme, lem-weil-pbc-lft-base-change, lem-weil-pbc-open-immersion-base-change and lem-sfb-finite-type-composition-base-change. Their statements supply respectively K, the universal property, the group diagrams, lft for H_K, openness of U_K, and finite type for U_K/K. The last lemma is applied to U, already finite type by step 1, not to H. Base-changing the group diagrams is the explicit universal-property argument in the step.

For step 3, lem-sfb-lft-field-group-neutral-component explicitly allows arbitrary fields and non-quasi-compact lft groups and supplies the clopen finite-type subgroup C. I read lem-sc-lft-over-field-jacobson-space: it says closed points in every closed subset are dense, which is exactly what is needed for the closure of a point. The closed-point-residue-field node applies because K is algebraically closed and H_K is lft, without quasi-compactness. I read def-sc-group-scheme-translate and lem-sc-translation-automorphism; they give L_g(e)=g and its inverse, so maximal connected subsets correspond in both directions. The restriction of the scheme isomorphisms keeps nilpotents; no reduction is taken. The final finite selection is from the clopen partition restricted to the quasi-compact U_K, not from a claim that H_K has finitely many components. The step has fewer than 2000 characters and contains the full connectedness, rational-point and translation argument, with no separate unstated comparison lemma.

For step 4, lem-sc-group-scheme-separated-field states separatedness of every field group scheme, so it applies to C. The finite-type group ample-line node therefore has every required hypothesis. Each U_j is closed in U_K, hence quasi-compact, regardless of its being a proper open of D_j. The new 0B3E(2) node expressly accepts an immersion with quasi-compact source; a_j is the open immersion into C given by the component isomorphism. Thus the cited statement gives precisely the B_j needed. I checked the new node's notions against the scheme, immersion/open immersion, quasi-compactness, invertible module, absolute ampleness and tensor pullback definition nodes.

For step 5, I opened def-sc-invertible-module and def-weil-pbc-ample-invertible-module. The explicit finite product formula is a sheaf because the gluing axiom holds componentwise; its local restriction to each U_j is B_j, so local rank one is preserved. Tensor powers also restrict componentwise; zero extending a section gives exactly its original nonvanishing locus on one component and empty loci on the others. This directly supplies the absolute ampleness witnesses. It is elementary gluing on disjoint opens, not a new lemma or an application of an undocumented ampleness-locality theorem.

For step 6, I read lem-sfb-ample-existence-field-extension. It asserts existence of an absolutely ample invertible module on X from existence on X_K for any field extension and with no finiteness restrictions. This is exactly the conclusion used for U; no Galois descent datum or descent of B is asserted. All off-unit citations are declared in split_report.tool_uses as generic tools.

I tested the empty U (empty affine cover and vacuous ample witnesses), the trivial group, finite nonreduced groups alpha_p and mu_p, and an infinite constant discrete group (only finitely many components meet a quasi-compact open). I also considered E times an infinite constant group, with E an elliptic curve and U a proper open in one component: this checks why U need not be a subgroup and why the restriction theorem is necessary. Imperfect k causes no gap because the argument is made over its algebraic closure and 0BDC descends existence along arbitrary field extensions. For the new lemma I checked identity maps, empty source, closed immersions, and proper opens; dropping quasi-compactness would fail the absolute definition, so that hypothesis is retained.

The B-E checklist found no hollow statement, added hypothesis, cycle by construction, duplicate, unsupported tag-only invocation or elementary new node. The only new node is statement-only. All non-elementary steps cite the statements they use, with verbatim quotations in citations.json. No proof step exceeds 2000 characters. The preliminary server review_split returned PASS. Full dry run and push follow this report.

## Unfinished

None in this one-level split. The new statement-only node joins the stage-1 queue as required.
