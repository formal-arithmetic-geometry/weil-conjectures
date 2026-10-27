# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-coherent-hyperplane-restriction-sequence.json: statement, split; statement unchanged; six proof steps, no new nodes, no Mathlib leaves.
- citations.json: one entry for each of the 20 step/node uses, quoting the actual complete statement verbatim. Full statements were retained so the multiple clauses taken from the common-hyperplane node are visible together.
- report.md: this report and direct-delivery self-review.

The sandbox initially contained only dispatcher markers. I copied the live item once and retained all imported fields, its previous searches, source, statement dependencies, creation metadata and blueprint ancestry. I added the NQ searches as actually logged in searches.jsonl.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and both hyperplane node ids, and for hyperplane/Hyperplane and the projective-space notions, did not find a declaration stating the item. The projective-space files found by the broader notion search provide constructions and cohomology, not this theorem. No compiler was run.

## Literature wanted

None. The relevant Stacks sources are present locally.

## Findings and changes

The imported statement is consistent with its sources; no statement dispute or correction is needed. Its proof was empty. I read varieties.tex, lemma-hyperplane (089Z), lemma-exact-sequence-induction (08A0), the immediately following finite-family remark, and remark-exact-sequence-induction-cohomology (0EGK). I also read coherent.tex, lemma-coherent-Noetherian (01XZ) and lemma-cohomology-projective-space-over-ring (01XT in section 01XS); constructions.tex, lemma-apply-modules (01MT) and its preceding frame calculation; modules.tex, lemma-tensor-product-pullback (01CD); and algebra.tex, lemma-Noetherian-permanence (00FN).

The DAG already has lem-sfb-coherent-regular-hyperplane-restriction, created for the free-quotient regularity bound. Its statement is more general than this item's hyperplane/exact-sequence clauses: it simultaneously treats a finite family and explicitly includes coherence, twist identifications, cohomology comparison, naturality, and multiplicative restriction. Reusing that node is required by the duplicate rule. I did not recreate associated-prime avoidance or move the current item into a new clause node. The only extra work is normalizing multiplication across the twist identifications and obtaining surjectivity on linear sections. To obtain the latter for the SAME hyperplane, I apply the finite-family node to F and O_P, rather than choosing another hyperplane for O_P. The cohomology sequence at twist 1 for O_P and H^1(P,O_P)=0 give surjectivity.

The helper has no proof dependencies in the read repository, so this reuse creates no cycle. The three substantive off-unit tools are the coherent finite-type criterion, tensor pullback, and projective twist cohomology, together with the frame formula for twist multiplication. Each is declared with a specific purpose in split_report.tool_uses. The finite-type algebra Noetherian theorem is already a Mathlib leaf. This stays below the existing Hilbert/regularity prerequisite route; it changes no chapter or unit statement or route. The inherited blueprint.from.node is null, exactly as tools/blueprint_refs.py ancestor reports for this existing ancestry; its detailed place and via list are retained.

## Mathlib and blueprint searches

The five new NQ msearch calls are exactly those in searches.jsonl and appended verbatim to the item's mathlib_searches: LeanFinder for coherent hyperplane restriction, Loogle for "hyperplane", grep for hyperplane|regularHyperplane|hyperplaneRestriction in AlgebraicGeometry, LeanSearch for a general hyperplane acting as a non-zero-divisor, and a second LeanFinder phrasing in terms of associated-prime avoidance. All services answered. I read the returned hits: they concern convex hyperplanes, vector-space projectivization, Proj structure sheaves/topology, unrelated derived vanishing, or ring regular sequences. None states this coherent-module hyperplane theorem. Ring regular-sequence declarations alone do not choose a common projective hyperplane or identify its cohomology sequence. The original item's five historical searches were retained after reading their recorded results.

Whole-DAG searches included 089Z, 08A0, 0EGK, hyperplane, associated points, linear forms, global sections of twists, and homogeneous polynomials. tools/blueprint_refs.py searches for hyperplane, 089Z, 08A0, regular hyperplane, twist tensor and projective-space-twist-cohomology were read. No blueprint node states this item in another form. The DAG search exposed the existing finite-family node and existing tensor and cohomology tools; none was duplicated. The report's unused broad search hits are not proof citations.

## Not duplicates

No new nodes are created. lem-sfb-coherent-hyperplane-restriction-sequence vs lem-sfb-coherent-regular-hyperplane-restriction: the latter already supplies the more general finite-family restriction/cohomology theorem and is cited directly. This item's additional explicit clauses are multiplication-compatible choices of all integer twist identifications and surjectivity of linear-section restriction; those are proved in steps 3 and 5 using existing nodes. No edit to the existing helper is included.

## Review by NQ

I checked the actual JSON statements and the Stacks passages above, not just the dependency names. There are no new-node statements to audit. The item retains every original hypothesis (infinite field and n at least 1) and every conclusion, including all integer twists, every nonnegative cohomological degree, the initial zero term, the restriction description, linear-section surjectivity and multiplication compatibility.

Step 1 uses def-pc-proj for the actual affine localization charts, pqf-def-locnoeth for what the local Noetherian assertion means, and pqf-def-coherent for quasi-coherence and finite type. The chart ring is computed by explicit inverse monomial substitutions. lem-weil-pbc-finite-type-algebra-noetherian says precisely that a finite-type algebra over a Noetherian ring is Noetherian; a field has only two ideals. pqf-lem-coherent-ft-locnoeth then says exactly that a quasi-coherent finite-type module on this locally Noetherian scheme is coherent. It is used only after that hypothesis has been verified. Thus the second module O_P really satisfies the finite-family theorem's input assumptions.

Step 2 cites the STATEMENT of lem-sfb-coherent-regular-hyperplane-restriction, not its empty proof. That statement expressly gives a nonzero linear form, H isomorphic to lower-dimensional projective space, coherent pullbacks, and the common family construction. Its infinite-field and n hypotheses match ours. def-pc-zero-scheme defines the ideal as the image of the dual map; def-pc-projective-space-twist gives the local frame. In that frame the image is (s/T_j), proving that its closed subscheme is the same H. No set-theoretic factorization is substituted for scheme-theoretic equality.

Step 3 is the written elementary normalization argument. lem-pc-twist-tensor gives the actual basis multiplication for EVERY pair of integers; lem-weil-pbc-module-pullback-tensor gives the natural tensor comparison; def-sc-invertible-module provides dual line bundles. Together with the explicit gluing frames in def-pc-projective-space-twist, these let theta_1 be extended by powers and duals. The local coefficient c is a UNIT, which is necessary for negative d. The equality c^d c^e=c^(d+e) verifies multiplication, including mixed and negative degrees, and transition powers check gluing. I did not assume that independent degreewise isomorphisms were automatically compatible. This is one routine frame computation from cited statements, not a hidden new theorem.

Step 4 again uses the common-hyperplane node's actual short exact sequences, natural cohomology identifications and restriction arrows. pqf-def-cohomology expressly states the long exact cohomology sequence for a short exact sequence, which supplies the initial zero and all adjacent terms. No vanishing hypothesis on F is introduced. The coherent pushforward/cohomology comparison is part of the cited common-hyperplane statement, so it is not inferred merely from a definition of cohomology.

Step 5 uses that SAME node for the second family member O_P, at d=1, and its cohomology sequence. The explicit map B tensor_A A to B justifies i^*O_P=O_H without an extra lemma. lem-pc-projective-space-twist-cohomology states that all positive cohomology at nonnegative twist vanishes; hence its degree-one group at twist zero is zero even when n=1. Exactness yields precisely the claimed surjectivity, without using a vanishing theorem for arbitrary coherent F.

Step 6 uses the pullback definition's actual unit and the section formula in lem-weil-pbc-module-pullback-tensor, which explicitly sends the pullback of a tensor of sections to the tensor of their pullbacks. The twist-tensor basis map then gives the displayed equality for u and v. Step 3 ensures that changing to the lower projective space preserves this equality. These two final compatibilities are concrete calculations, not an unspecified transport.

I tested the edge cases n=1 (H is P^0), F=0 (the second family member still gives a nonzero hyperplane), F a skyscraper module (the finite-family theorem chooses a hyperplane avoiding its associated point), d=0 and negative d (dual frames with unit coefficients), and positive characteristic infinite fields (no characteristic restriction occurs). Surjectivity at n=1 uses H^1(P^1,O)=0, not any assertion that negative twists on P^0 have no global sections. At no point is n=0 assumed for the original P. Finite fields are outside the hypothesis and are not silently included. The section products have their correct target G(d+1).

B1--B10: no new nodes, no hollow definitions or new Mathlib leaves; all original provenance is retained and all additional searches really ran. C1--C8: each non-elementary input is a cited statement, all 20 citations are quoted verbatim, the only elementary steps are the explicit frame and section computations, the reused helper has no path back to the item, and generic off-unit tools are declared. D1--D5: no new node restates the item or a clause; the overlapping EXISTING finite-family node is reused as mandated, while the extra compatibility and surjectivity arguments remain in the proof. E1--E7: hypotheses were checked at the steps above, the scheme structure and module pullback are the actual objects stated, and no source error was found. Each step is shorter than 2000 characters; I also checked them for hidden subclaims regardless of length.

## Unfinished work

None in this one-level split. Proving the pre-existing unsplit finite-family node remains its own assigned DAG work. No Lean file, compiler, Lake, repository git command, launcher edit, or agent delegation was used. The required server dry run and delivery follow this report.
