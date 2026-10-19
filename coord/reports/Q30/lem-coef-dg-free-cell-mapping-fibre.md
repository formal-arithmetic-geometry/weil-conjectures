## Worker report

Item: lem-coef-dg-free-cell-mapping-fibre. Group: Q30. Stage 1 only, 2026-10-17.

### Files written

- dag/nodes/sec-six-functors/lem-coef-dg-free-cell-mapping-fibre.json: split into seven proof steps, no Mathlib match. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quote for each of the 22 citations in the seven steps.
- report.md: this report. searches.jsonl contains the actual search-command records.

### Attachments

None. Searched the slopmaster2 project under WeilConjectures/ for the exact item id and for freeCell/free_cell/mappingFibre/mappingFiber, dgcat, semi-free, differential graded categories and dg-category vocabulary. No declaration states this theorem. The item has no Lean declaration in its live node. No Lean was written and no compiler, Lake or build tool was run. The upstream master source is not treated as evidence of completion.

### Sources requested

WANTED: Drinfeld, DG quotients of DG categories, https://arxiv.org/html/math/0210114 (PDF https://arxiv.org/pdf/math/0210114), sections 13.4-13.6, for lem-coef-dg-free-cell-mapping-fibre.

WANTED: Hovey, Model Categories, https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf, Theorem 2.3.11 and sections 5.2-5.4 (especially Definition 5.2.7, Theorem 5.2.8, Corollary 5.4.4, Proposition 5.4.7), for lem-coef-dg-free-cell-mapping-fibre.

Both were read online, without downloading into the read-only repository. Neither was found in the local literature inventory. The proof_origin is agent: Drinfeld supplies the semi-free construction and lifting argument, but does not state the complete enhanced fibre theorem. The simplicial-resolution proof here supplies that refinement using the existing model-category nodes. No Stacks tag states this dg-category mapping-space calculation; no SGA source is used.

### Issues found and corrected

The shared snapshot did not contain the assigned item. It does occur, unsplit, in the newer read-only mirror /home/ubuntu/weil-nt-live-dag/nodes/sec-six-functors/, together with its parent lem-coef-dg-quotient-hom-cone. I copied the assigned node from that mirror, preserving its chapter, unit, creation and ancestry metadata, and used current mirror statements for citations. This is a shared-view synchronization discrepancy; no git command or write was made in the shared project, live project, source checkouts or launcher.

The imported statement had doubled TeX backslashes and literal newline escapes. I normalized these to actual TeX and line breaks, explicitly said that the base ring is Z (already required by the cited dgcat model), and cited lem-coef-projective-chains-monoidal-model for the enhanced localization D(Z). The last addition fixes a notion-level citation gap: def-weil-abstract-derived-category alone defines the ordinary derived category, not its mapping spaces. These changes preserve all objects, hypotheses and conclusions. There is no mathematical statement dispute.

The original item had no proof. In particular, a bijection between strict extensions and choices dh=F(z) would not by itself prove the mapping-space assertion. Steps 2-4 retain a common simplicial target resolution and check its Hom matching maps, so that the strict fibre really computes the derived fibre. The argument does not assume the target has cofibrant or flat Hom complexes, does not replace quasi-equivalences by Morita equivalences, and handles arbitrary small I without invoking a finite-product statement for an infinite product.

I read the six-functor chapter and sk-prop-sf-biduality-general unit records, and the current main-20261015 prop-coef-integral-exceptional-adjoint statement and proof. This is infrastructure for paragraph 2's derived Hom coefficient adjunction through the pre-existing quotient ancestry. It changes no chapter or unit route and is not that unit's key statement, so no unit record is edited. Blueprint searches (using tools/blueprint_refs.py, also with its read-only NODES reference set to the newer mirror for ancestry) returned no match for free cell, mapping fibre, cosimplicial frame or prescribed differential. The mirror resolves the ancestor as prop-coef-integral-exceptional-adjoint. There are no new nodes to compare for duplication. All proof inputs are existing generic tools in this same unit; no off-unit replacement route is used.

### Mathlib search

Ran the required msearch.py commands for the item: LeanFinder, Loogle, source grep and LeanSearch, followed by a differently phrased LeanFinder search and a logged grep locating the ordinary HomComplex constructors. Each actual query and the command's result record is appended to the node without inventing searches. All services returned successfully. The first semantic search found homotopy cofibres of ordinary complexes; LeanSearch found ordinary cocycle and mapping-cone constructors; the second semantic search found Dold-Kan projection homotopies and nullhomotopies involving K-projectives/K-injectives. Loogle and the focused whole-Mathlib dg-category grep returned no hits. Read HomotopyCofiber.lean:12-38, HomotopyCategory/HomComplexSingle.lean:35-92, DoldKan/HomotopyEquivalence.lean:35-92, and Enriched/Basic.lean:58-75. These do not state this dg-category theorem. The already existing Mathlib leaf lem-coef-sset-anodyne-pushout-product is reused; its precise declaration was read at AnodyneExtensions/PushoutProduct.lean:95-103.

## Not duplicates

No new nodes. The proof uses lem-coef-dgcat-free-cell-calculus, lem-coef-dgcat-model-structure, lem-coef-cosimplicial-frame-mapping, lem-coef-reedy-model-structure, lem-coef-projective-cochain-monoidal-model, lem-coef-projective-chains-monoidal-model, lem-coef-kan-quillen-right-proper and the existing Mathlib leaf lem-coef-sset-anodyne-pushout-product. No clause of the item is moved into another node.

## Review by Q30

I read Drinfeld 13.4's definition of a relative semi-free dg category, 13.5's construction, and 13.6's surjective-quasi-equivalence lifting statement and its final complex calculation. I also read Hovey's frame definition and construction (5.2.7-5.2.8), the dual Quillen assertion in 5.4.4, and the two function-complex comparisons in 5.4.7. Drinfeld alone only supplies strict lifting, so I did not attribute an enhanced mapping-space theorem to him. The proof is the explicit refinement above. There are no new nodes whose sources or standalone statements need separate review.

Step 1 uses precisely the dgcat model's description of trivial fibrations, the cochain model's generating sphere-to-disk cofibrations, and the free-cell node's word construction. I checked their statements, not their proofs. The square of complexes is written explicitly: v maps to a(z), u on the bottom to b(e); closure dz=0 is exactly what makes its top map a chain map. Every new arrow has old endpoints, so no object-lifting lemma is silently needed. Independence of the generators and the free word evaluation give a simultaneous filler even if several arrows share endpoints or are loops. Composition of left lifting properties proves the claimed cofibrancy. This is an argument for the item, not a new restatement lemma.

Step 2 applies the frame theorem to the opposite model category. Its hypotheses hold because the dgcat-model statement says all objects are fibrant and Step 1 says both sources are cofibrant. The resulting restriction is a Kan fibration because a cofibration in the original category is a fibration between fibrant objects in its opposite. The cited frame statement expressly computes localization mapping spaces and makes the comparison natural. The Reedy node explicitly permits the opposite model and a fixed degree-zero factorization; this justifies the functorial choice with E_0=E. Reversal of the localization universal property accounts for the variance. No assertion about strict fibres is made before this fibration is established.

Step 3 uses the same dgcat fibration criterion to prove, rather than assume, that the complexes K_i form a simplicial resolution. I checked that matching Hom complexes are the limits of the individual Hom complexes at the chosen compatible object tuples: composition and differential are componentwise and the limit universal property gives exactly that object. Thus Reedy fibrancy gives degreewise surjective matching maps. Quasi-equivalence of the coaugmentation gives the required quasi-isomorphisms. The complex model identifies these surjections as fibrations; the Reedy and frame nodes then give the frame criterion. This remains true for s=t and for a target with nonflat Hom groups.

Step 4 uses the exact cochain indexing of the projective-cochain statement: S^{n+1} is Z in degree n+1, while D^n has identity differential from n to n+1. The sphere represents Z[-n-1], not its opposite shift. The complex-model criterion gives cofibrancy (the Hom complexes into acyclics are respectively shifts and contractible complexes). The opposite frame theorem supplies a Kan fibration Y_i -> X_i. The enhanced-localization clause of projective-chains-monoidal-model identifies X_i with the D(Z) mapping space actually in the item. The acyclic disk is equivalent to zero, so Y_i is contractible with a specified zero point; this is stronger than merely knowing its set of components.

Step 5 is elementary after the cited free-word universal description and Kan pullback rule: an extension gives exactly independent images h_i, and commuting with d means dh_i=F(z_i). This equality is imposed in every simplicial degree and respects every operator. The disk/sphere description identifies these choices with the fibres of the p_i from Step 4. Infinite products of Kan fibrations are handled directly by choosing componentwise horn fillers. The finite-product clause of the frame node is not misused for an arbitrary small set.

Step 6 uses the existing pushout-product leaf and Kan model statement. The product/exponential adjunction turns an exponential horn lift into the anodyne pushout-product in the leaf, proving the endpoint fibration. The precise exponential/pushout-product source is Hovey 3.3.1-3.3.2, which I checked while correcting an initial source-number typo in this step. The written min contraction proves the starting-point path space contractible; it is not asserted without explanation. Thus both Y_i and P_0 X_i are fibrant replacements over X_i of its same zero point, and the Kan node explicitly grants independence of the homotopy-pullback replacement. Pulling back at x_i gives exactly paths from 0 to F(z_i). Products are checked componentwise, including empty fibres and the empty family; no new non-elementary product lemma is hidden here.

Step 7 keeps the simplicial family over the entire base. I checked the free-word formula over an arbitrary simplex sigma and its restrictions, so it retains the faces and degeneracies encoding coherent variation of F. Every target structure map is a quasi-equivalence by its coaugmentation, so the resulting complexes vary by quasi-isomorphisms. The cited frame node includes naturality on localization mapping spaces; the Kan node gives the natural replacement-independent pullback. Functorial Reedy choices and applying a target functor to the very same h_i and z_i establish target naturality. No claim about noninvertible natural transformations of dg functors is added: the item concerns mapping spaces.

Small cases checked: I empty gives j the identity and its fibre a point; a nonzero cohomology class F(z_i) makes the corresponding path and extension fibre empty; z_i=0 gives the expected loop space of Map(Z[-n_i-1],K), matching an unconstrained closed degree-n_i arrow; n_i=-1 gives paths from zero to a degree-zero identity as used by the existing parent. A zero Hom complex gives a point. Several generators with identical endpoints remain independent because there are no imposed relations. All integers, loops, empty B (necessarily I empty) and nonflat target Hom complexes are admitted. No hypothesis is added to avoid one of these cases.

Finally I audited B-E against the actual statements: no new-node shape/search/duplicate issue arises; every non-elementary tool is an existing cited statement; proofs are not borrowed from interiors of nodes; there is no quotient-node citation back to the parent; all argument is in the item's steps. Every citation quote in citations.json is a verbatim part of its node's statement and includes the relevant hypotheses. Dry-run results are recorded below.

### Completion

All mathematical work for the split is complete. No new node, Mathlib leaf, unit edit, attachment or statement dispute remains. Delivery is reserved for the fresh second reader.

### Dry-run verification

The required deliver.py Q30 lem-coef-dg-free-cell-mapping-fibre --no-push printed OK (not pushed), commit 3606530b4d, with preflight passed. I then corrected the step-6 source number to the checked Hovey Theorems 3.3.1-3.3.2 and recorded the extra actual candidate-location grep. The final handoff is checked by rerunning the same dry-run command on these files. A separate read-only dependency traversal checked 129 reachable nodes, found no missing or merged input and no path back to the item. Nothing is pushed.

## Second reading by Q30

- Step 1 checked against Drinfeld §§13.4–13.6 and the cited dg-category, projective cochain, and free-cell statements: the sphere/disk lifting square has the stated degrees and differential, independent fillers give the simultaneous free extension, and the cofibration conclusion is valid.
- Step 2 checked against Hovey §§5.2–5.4 and the cited frame/Reedy/model statements: the opposite-model variance and restriction fibration are valid; I made the reversed map (j^{\mathrm{op}}:\mathcal B[e_i]\to\mathcal B) explicit.
- Step 3 checked against the Reedy matching formulas and the dg-category limit description: the matching Hom complex is the compatible Hom limit, the induced map is degreewise surjective, and the resulting simplicial complex is the required frame without a flatness hypothesis.
- Step 4 checked against the projective cochain model and Hovey's function-complex comparison: the shifts (S^{n_i+1}=\mathbf Z[-n_i-1]), disk contraction, Kan fibration, and contractible disk mapping space all have the claimed indexing.
- Step 5 checked against the free-word universal property and the Kan homotopy-pullback statement: extensions are exactly independent (h_i) with (dh_i=F(z_i)), including infinite and empty (I), and the strict fibre is the product of the displayed pullbacks.
- Step 6 checked against the existing Mathlib anodyne pushout-product leaf and the Kan model statement: exponentiation gives the endpoint fibration, the minimum-map contraction gives (P_0X) contractible, and replacement independence identifies the pullback with paths from zero to (F(z_i)).
- Step 7 checked against the simplicial frame and Reedy naturality statements: structure maps of the target frame are quasi-equivalences by two-out-of-three, word assignments restrict over all faces and degeneracies, and the equivalence is natural in target functors and coherent (F)-variation.
- No new nodes were introduced; therefore there were no new-node statements to compare. Existing citations were searched in `dag/nodes` and each quote remains verbatim in its cited statement.

Changes made in this second reading: clarified Step 2's opposite variance by naming (j^{\mathrm{op}}); appended this source-by-step review. No statement dispute, hypothesis change, dependency change, or node deletion was needed. Edge cases checked directly include (I=\varnothing), (z_i=0), (n_i=-1), loops and repeated endpoints, zero Hom complexes, empty (mathcal B), and nonflat target Hom complexes.

Second-reader dry run: `OK (not pushed) deliver/Q30/lem-coef-dg-free-cell-mapping-fibre at 86207912b2: preflight passed`.

After the first delivery attempt, the current upstream `lem-coef-dgcat-model-structure` statement had gained an explicit citation to the projective cochain model in its second paragraph. I refreshed the four affected citation quotes (steps 1, 2, 3, and 7) against that exact current statement; no proof text or mathematical dependency changed.

Second-reader dry-run after citation refresh: `OK (not pushed) deliver/Q30/lem-coef-dg-free-cell-mapping-fibre at 2d19c99eb0: preflight passed`.
