## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-quotient-noetherian-descent.json: item, statement unchanged, eight complete proof steps, status split.
- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-module-finite-product.json: statement, Mathlib leaf isNoetherian_pi, Mathlib/RingTheory/Noetherian/Basic.lean:177 (full declaration read at lines 175–183).
- citations.json: one entry per cited node per item step, with the verbatim statement. searches.jsonl records the actual msearch calls. No Lean was written or compiled.

## Attachments

None. Searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact item tag, Eakin, Noetherian subrings, finite quotients and Noetherian descent found no declaration stating the item. In particular, upstream sorry declarations are not treated as proofs. Mathlib's IsNoetherianRing.of_finite is ascent, and isNoetherian_of_injective requires identical/isomorphic scalar rings; neither is finite injective descent.

## Wanted sources

WANTED: P. M. Eakin, Jr., The converse to a well known theorem on Noetherian rings, Math. Ann. 177 (1968), 278–282, main theorem, for lem-per-finite-quotient-noetherian-descent.

WANTED: H. Matsumura, Commutative Ring Theory, §3, Theorems 3.6 and 3.7 (Formanek's module argument and Eakin–Nagata), for lem-per-finite-quotient-noetherian-descent. The publisher preview was consulted through https://api.pageplace.de/preview/DT0400.9781107710450_A24418243/preview-9781107710450_A24418243.pdf; it was not downloaded into the project. Because neither source is in literature/, the delivered proof is explicitly marked agent-written.

The local Stacks file literature/stacks-project/examples.tex:1505–1512 explicitly invokes Eakin's theorem for a finite subring extension, but contains no proof. It is not misrepresented as a proof source. The new Mathlib leaf cites its actual declaration and full source lines directly, rather than assigning it a Stacks tag for the more restrictive Noetherian-base statement.

## Findings and corrections

The imported item is true as written. Its antecedents, including injectivity, are preserved exactly. There was no proof in its record. The existing parent lem-per-finite-quotient-strict-local-invariants, Step 1, needs precisely this descent, and its existing ancestry records the finite quotient/local-uniformization use. I read the item, that parent step, the current main-20261015 blueprint file of lem-per-artin-gabber-affine-curve, the recorded chapter and the unit sk-p-dl-a1-perverse. No unit or chapter route is changed.

The proof first works with all quotients A/IA that are not Noetherian over B. Maximality is selected among their extended A-ideals, using Noetherianity of A, not among arbitrary B-ideals (which would assume the conclusion). Passing to the annihilator quotient R makes the selected module faithful. The equality JA=I_0A is proved before claiming that every nonzero R-ideal gives a Noetherian module quotient. The maximal-faithful-quotient argument uses finite generation to keep the union of a chain faithful. It does not infer faithfulness of arbitrary unions without this check.

No mathematical correction or statement dispute was needed. The report marks the missing sources and proof origin rather than silently attributing an unavailable proof to the literature. The erroneous first Loogle product pattern returned unknown identifier Pi, which is recorded as no match for that query, followed by a successful quoted-name query; no service failure is recorded as evidence of absence. Existing searches in the item are retained, and the Q04 searches are appended.

## Unfinished work

None in this one-level split. There is one new node and it is an exact Mathlib leaf, with no new unsplit theorem. The maintainer's independent review and eventual Lean proof remain subsequent stages of the project.

## Not duplicates

lem-per-noetherian-module-finite-product vs lem-weil-pbc-noetherian-submodule-finite: the existing statement assumes a Noetherian scalar ring and a finite module. The new statement allows any commutative scalar ring and assumes only that the factors are Noetherian modules; applying the existing statement to the evaluation target before knowing R Noetherian would be circular.

lem-per-noetherian-module-finite-product vs lem-weil-pbc-noetherian-finite-module-acc: the existing statement also requires the scalar ring to be Noetherian and does not state product closure for modules over an arbitrary scalar ring.

lem-per-noetherian-module-finite-product vs lem-trf-product-noetherian-flat-mittag-leffler: that statement concerns flatness and the Mittag-Leffler property of arbitrary products of the scalar ring, with R Noetherian; it does not assert Noetherianity of finite products of arbitrary Noetherian R-modules.

No node with the new id exists. Whole-DAG searches for the declaration names isNoetherian_pi/isNoetherian_prod and for statements about finite products/direct sums of Noetherian modules found no existing node stating the new fact. Many text hits were only recorded search queries in unrelated nodes. blueprint_refs.py searches for Noetherian product, Noetherian module and Eakin found zero blueprint nodes. The exact item tag and notion searches in WeilConjectures/ found no attachment. Searches for faithful Noetherian module detection found no exact Mathlib result; its evaluation-map argument is three routine lines from the product leaf and is written in Step 2, not made into an unsplit duplicate of the item. The new node's blueprint.from is the computed ancestor lem-per-artin-gabber-affine-curve, and its via list includes the delivered item before the retained ancestry.

## Review by Q04

I read the local Stacks invocation in examples.tex and the publisher's Matsumura preview for the module argument, and checked the full pinned Mathlib declaration isNoetherian_pi at Basic.lean:175–183. The item agrees with the finite injective extension theorem, and the leaf agrees with Mathlib under a Ring R instance, additive groups and a finite indexing type. The leaf does not assume R Noetherian, does not claim infinite-product closure, introduces every object, defines Noetherian modules inline, and has no proof sketch in its statement. It is an exact leaf with empty proof and proof_deps, not a clause of ring descent moved into a child.

Step 1 uses the actual finite-generator definition in def-weil-finitely-generated-module. I checked quotient preservation by taking the inverse image of a submodule and mapping its generators, submodule preservation by the inclusion of submodule lattices, and passage to R/J by equality of submodules and coefficient classes; these are elementary arguments included in the step.

Step 2 cites the new finite-product statement for V^s and def-weil-pbc-noetherian-ring for the conclusion. I checked injectivity of evaluation using the chosen generators and faithfulness, then checked that generators of the image of each ideal lift to generators using injectivity. No finiteness of the underlying set of V is used. This is the routine evaluation argument, not an uncited appeal to a faithful-module theorem.

Step 3 cites lem-weil-pbc-noetherian-ideal-set-maximal, whose statement gives a maximal element of every nonempty set of ideals of a Noetherian ring. Its ring here is A, already Noetherian by hypothesis, and its objects really are A-ideals IA. The set contains zero only under the explicit contradictory assumption that A is not Noetherian as a B-module. Images of the finite B-generating family generate M.

Step 4 uses no black-box theorem: it proves both inclusions in JA=I_0A and explicitly verifies that any nonzero ideal H of B/J has a preimage L with LA properly larger than I_0A. The calculation of M/HM follows from the preimage LA. This supplies faithfulness and the exact nonzero-ideal hypothesis used later, even with zero divisors and nilpotents.

Step 5 cites lem-weil-pbc-zorn-lemma, whose statement includes empty chains. I checked that zero belongs to the family, nonempty chain unions are submodules, the finitely many rm_j all lie in one chain member, and annihilation then forces r=0. I explicitly covered the empty chain by zero and the empty generating family by choosing any member of a nonempty chain. This verifies the cited Zorn hypotheses rather than assuming a maximal quotient. The submodule correspondence used for Q/U is spelled out by its inverse image.

Step 6 cites lem-weil-pbc-noetherian-submodule-finite only after Step 2 has made R Noetherian under the temporary assumption that Q is Noetherian. Its other hypothesis is the already established finite generation of M. I checked the canonical surjection M/HM to Q/HQ by its scalar-sum formula. Quotients preserve Noetherianity by the written Step 1, so this step takes nothing from the proof of a cited node.

Step 7 is the remaining actual argument, not a reference to Eakin–Nagata or to a Formanek black box. Nonfaithfulness of Q/U supplies a nonzero scalar annihilating it. The principal ideal (a) is nonzero because a is nonzero. Generators multiplied by a generate aQ; generators of U/aQ lift and, together with those of aQ, generate U. The case U=0 is separate. Step 8 applies the proved Noetherianity of the B-module A to i(H) and lifts its generators using the original injectivity. Its cited Noetherian-ring definition says exactly the asserted conclusion. citations.json contains the actual statements for every cited node at every step.

For delivery-errors B–E, I checked complete independent leaf statements, correct notions and hypotheses, source places, actual search results and Mathlib source lines, no duplicated or missing citation, no circularity or reliance on another node's proof, and no hidden ring-theoretic input. The generic existing lemmas are Mathlib leaves, so no off-unit tool declaration is needed. Every proof step is under 900 characters; the proof does not hide a long separate lemma in a step exceeding 2000 characters.

Small cases: the zero target ring forces the zero source ring by injectivity, and the empty-product clause is valid. The leaf with one factor is tautological; with empty index it is the zero module, which is Noetherian over every R; with R non-Noetherian and all factors zero it remains valid. The item applies to k[t²,t³] contained in k[t] (two module generators 1,t) and to a finite nilpotent extension, without any domain assumption in the argument. Dropping injectivity fails for k[x_1,x_2,...] mapping onto k. Dropping module finiteness fails for k[x,xy,xy²,...] contained in k[x,y]: the source ideal (x,xy,xy²,...) is not finitely generated, since its degree-one-in-x part has independent monomials xy^n and multiplication by a nonconstant source monomial raises the x-degree. These checks confirm the hypotheses are substantive and that the proof has introduced none. I corrected the initial ambiguous Loogle query by an exact-name query and made every quotient/faithfulness check explicit before delivery.
