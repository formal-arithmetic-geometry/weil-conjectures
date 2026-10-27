# Q82 stage-1 delivery

Item: lem-trf-infinitesimal-vanishing-section-lifting

## Files written

- dag/nodes/sec-trace-formula/lem-trf-infinitesimal-vanishing-section-lifting.json — statement, split into eight steps; no Mathlib match.
- No new nodes and no new Mathlib leaves.
- citations.json contains the 21 verbatim statement excerpts for the eight proof steps. searches.jsonl contains the actual recorded search outputs. The existing item's older search records are retained.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, infinitesimal vanishing, formal functions, image stabilization and section lifting found no finished declaration of this item. The existing MLCohomologyPowersIdeal and FormalFunctionsLocalStalkComparison declarations are tools with different statements, not attachments of the item. The existing lem-sc-lift-sections-h1-vanishing is about abelian etale sheaves, so it was not used for Zariski module cohomology; the module section-boundary theorem supplies the correct interface.

## WANTED

None. All sources needed for the proof are present under literature/stacks-project/.

## Problems found and corrections

The imported statement is correct and is unchanged. It isolates the degree-zero last paragraph of Stacks 0D2M after supplying its layer vanishings as hypotheses. The original node was statement-only, not an accepted proof.

The crucial distinction is between arbitrary compatible formal sections and an algebraic section over the local base. The proof uses 02OB's equality with the image of actual cohomology, not just its Mittag-Leffler clause and not an unsupported inference from completion. It needs only a lift to the single finite level 1+c. It assumes neither flatness of f nor completeness of A, and it never assumes H1 of the closed fibre vanishes. The hypothesis starts at n=1, which is precisely the kernel of Q_2 -> Q_1.

The statement and the proof route remain those of the assigned item. I read dag/chapters/sec-trace-formula.json, dag/units/sk-i-curve-zero.json, SETUP.md's three levels, and the latest blueprint proof of lem-trf-local-term-locality. This node is a generic Noetherian cohomology subargument in the inherited 0D2M/0D2N ampleness branch, not a change to the contracting-correspondence argument of the unit. Generic statements from other units are declared under split_report.tool_uses, leaving the maintainer's tool_uses field untouched.

## Not duplicates

No new nodes. Existing tools were reused after searches through the whole DAG and blueprint. In particular, lem-weil-pbc-ml-cohomology-powers-ideal already gives the required image equality; lem-weil-pbc-formal-functions-local-stalk-comparison already gives the uncompleted germ-to-pullback map; and lem-weil-pbc-closed-immersion-unit-quotient already identifies the quotient and its projection with fibre pullback. No separate infinitesimal lifting, product exactness, coherence-of-a-line-bundle, or neighbourhood-spreading lemma was created.

## Mathlib searches

The five new searches are exactly those logged in searches.jsonl: two genuinely different LeanFinder formulations, Loogle on AlgebraicGeometry.IsProper, a grep for formal-functions/ML/cohomology-ideal-power terminology in AlgebraicGeometry, and LeanSearch for the cohomological lifting criterion. All services answered. I read their results: properness stability is already represented by the existing proper-base-change node; structure-sheaf spreading and quotient-factorization morphisms do not identify images in H0 of line-bundle quotients and do not give the assigned criterion. The grep had no hits. There is no new Mathlib leaf claim.

## Review by Q82

I read coord/delivery-errors.md B through E in both its original and merged copies. I checked sources with the node statements open, rather than relying on a cited node's proof. The source for the item is coherent.tex, Tag 0D2M, from its initial local-base-change paragraph to its final degree-zero paragraph (lines 5995-6089). I also read 02OB's image equality (coherent.tex 5553 onwards), the uncompleted part of 02OD (5750 onwards), 01XZ's coherence criterion (2225 onwards), 00FN in algebra.tex, 01T6 and proper base-change permanence in morphisms.tex, 01JU in schemes.tex, 08KS in modules.tex and 01E4 in cohomology.tex. There are no new-node sources to certify.

Step 1 uses the affine-open Noetherian criterion, the canonical-local-ring morphism, localization permanence and the definition of locally Noetherian. Their statements give R Noetherian, A = R_p, preservation under localization and the one-chart cover criterion, respectively. This establishes the ring hypothesis needed later, without taking Noetherianity of a stalk from a lemma that merely asserts finite generation of its maximal ideal.

Step 2 uses proper base change, the definition that proper implies finite type, and the finite-type Noetherian theorem to obtain locally Noetherian Z and X. The invertible pullback node applies to h without a flatness assumption. The invertible definition gives quasi-coherence and rank-one local trivializations, so the finite-type/coherent equivalence on a locally Noetherian scheme makes both E and F coherent. Both applications have the required locally Noetherian ambient scheme.

Step 3 uses only the rank-one trivializations in the invertible definition. It writes out the kernel and the canonical multiplication isomorphism on each trivializing open, where the sequence becomes the ordinary nested-ideal quotient sequence. These canonical maps glue. This is an elementary local calculation, not a new lemma and not a claim that the total space is flat over A. It explicitly identifies the kernel with the sheaf in the given vanishing hypothesis.

Step 4 uses the quotient base-change theorem with the actual ideal m, the closed-immersion unit quotient with F, and composition for tensor pullback. The first theorem states that this fibre inclusion has ideal J. The second states F/JF = i_*i^*F and identifies its projection with the adjunction unit. The fibre-product universal property and pullback composition identify i^*F with the original E_s. Taking global sections of a direct image is the definition, so no higher-cohomology pushforward theorem is being presumed.

Step 5 uses the module section-boundary theorem. It is stated on any ringed space, for the same Zariski module cohomology as the item. Its equivalence between zero boundary and an actual section lift applies to each exact sequence from step 3. Vanishing of H1(X,K_n) therefore makes each successive map surjective. The finite induction has an explicit base n=1 and an explicit step; it claims no lift using a missing n=0 vanishing.

Step 6 uses precisely clause (2) of the existing ML node, which is Stacks 02OB(3): Im(tau_{k,n}) = Im(rho_n) for k >= n+c. Here n=1, k=1+c, I=m, p=0, g is proper, A is Noetherian and F is coherent. Thus the already constructed finite thickening lift lies in the image of an actual section. This is not a use of a mere definition of a Mittag-Leffler system, and the direction of the image equality is correct even when c=0.

Step 7 uses the actual uncompleted local-stalk comparison, the higher-direct-image presheaf theorem's explicit R0f_* = f_* clause, the stalk's representative-by-a-germ statement and the canonical local-spectrum morphism's containment in every neighbourhood. I verified that the comparison node explicitly sends germs of neighbourhood cohomology classes to their pullbacks; an abstract noncanonical isomorphism would not suffice. At p=0 these are sections. The hypotheses use coherence of E on Z, not just coherence of its local pullback, and step 2 established both. A representative of a^{-1}(u) therefore pulls back to exactly u.

Step 8 uses only pullback composition: restriction along the composite fibre map is restriction of h^*tilde(t), hence t. This verifies the conclusion for the original fibre, not a different closed subscheme of the local model.

I checked small cases: the zero fibre section is lifted by zero; an empty fibre has only that section; if m=0 the higher layers vanish and Q_1=F on the local base; if m is nilpotent the tower becomes constant and the same finite lifting argument applies; the stabilization bound c=0 uses the identity M_1 -> M_1 and requires no lifting steps. None requires f flat or A complete. All eight proof steps are shorter than 2000 characters. I checked B1-B10 (no new or hollow nodes, sources by tags, no invented searches, existing exact attachments ruled out), C1-C8 (all non-elementary inputs cited with verbatim excerpts, no circular reliance on this item, generic tool uses declared), D1-D5 (actual induction and image argument remain in the item, nothing relabelled into a new node) and E1-E7 (objects, hypotheses and canonical maps checked as above).

## Unfinished work

No mathematical part remains. The maintainer's independent review and landing remain external to this worker delivery.

## Dry-run repairs

The first dry run required longer citation excerpts for the affine-open Noetherian criterion and localization permanence. I replaced those two short excerpts with their full statements. I also checked tag-label mappings and corrected the proof source metadata to 01OW (locally Noetherian criterion) and 01W4 (proper base change). The mathematical argument and assigned statement are unchanged.
