# lem-sfb-finite-open-direct-image-ctf

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-open-direct-image-ctf.json`: existing statement, now split in seven steps; statement unchanged; no Mathlib match.
- `citations.json`: 15 verbatim statement extracts for the 15 step/node citations.
- `searches.jsonl`: actual searches recorded by msearch.py; their results were read.

There are **0 new nodes and 0 Mathlib leaves**. The sandbox initially contained only dispatcher brief markers, not an earlier split, report or search log.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for open-image/constructibility/Tor terminology. The closest declarations are `AlgebraicGeometry.ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar` and its Tor-only corollary in `SixFunctors/ProEtale/FiniteCoefficient/Derived/Stability.lean` (lines 234 and 256). They concern fixed module-valued sheaves and an explicit dimension bound, not the item's internal pulled-back condensed coefficient and constant-model predicate. Moreover their étale Tor input reaches `sorry` in `SixFunctors/Etale/Derived/Stability/DirectImage.lean` (lines 89 and 139). They do not justify ATTACH. No Lean was written or compiled.

## WANTED

None. The current blueprint, Stacks sources and Bhatt–Scholze PDF used here are present.

## Audit and changes

The item was statement-only. I retained its entire statement, source, blueprint provenance and imported searches, and supplied its proof. The current blueprint is `main-20261015`: I read the six-functors-basics chapter, the current `sk-thm-sf-ctf-stability/_section.md`, and paragraph (3) of `sk-thm-sf-ctf-stability-direct-images.proof.md`. The `dag/units/sk-thm-sf-ctf-stability.json` record still has the older finite-field chapter text; the item's current chapter and current blueprint route are the ones used. This item is not the unit's key statement, so no unit record is changed.

The important hypothesis issue is the arbitrary field. `det-cor-sf-direct-image-ctf-open-tor` assumes separable closedness, so I did not apply it. Instead the proof uses the existing arbitrary-field finite-constant projection theorem and the all-module Tor criterion. A relative bound on cd(j) is sufficient even when cd(k) is infinite. All derived comparisons are applied to bounded-below inputs, never to arbitrary unbounded-below objects.

I opened `lem-sfb-dc-lower-star-preserves` as suggested in the parent's review. It provides the general ring-object bounded-constructibility half. For this proof I used the more directly applicable existing `cor-fin-deligne-open-finite-coefficients` after étale descent. This avoids silently treating general locally finitely presented ring-object constructibility and constant-model constructibility as the same predicate. The finite-discrete equivalence is explicitly cited to identify the latter predicate. No source or step cites a prohibited SGA route.

The item has a null blueprint ancestor inherited from the parent delivery's Lean-module provenance. The ancestor command confirms null. I retained the specific `from.place` and `via`, filled `same_as: []`, and explained the realized finite-coefficient open sentence in split_report.blueprint. Blueprint searches for `open direct image`, `uniform Tor interval`, `finite constant`, `discrete`, `Tor amplitude`, and the prospective generic lemmas found existing tools, not another blueprint statement equal to this item. Whole-DAG searches by concept and the relevant tags found the nodes now cited. No new fact was introduced.

## Mathlib searches

I ran msearch.py with two distinct LeanFinder phrasings, Loogle `"TorAmplitude", "rightDerived"`, a whole-Mathlib grep for open immersion/constructibility/Tor/derived-image combinations, and LeanSearch for derived open-image stability. The hits were read. They concern constructible subsets, scheme morphisms, and underived structure-sheaf pushforward; none proves this finite-coefficient derived assertion. The Loogle query returned zero hits. All services used for this item answered successfully. The queries recorded in the node are copied from the real log; the inherited searches were preserved.

## Not duplicates

No new nodes. In particular, I reuse `lem-sf-open-tor-bound-arbitrary-field` rather than creating an arbitrary-field version of the existing separably-closed-field open-image corollary, and reuse `det-geo-open-finiteness-ii-amplitude` for the module-sheaf cd(j) bound rather than adding a separate forgetful-functor lemma.

## Review by NL

I checked the unchanged item against the current blueprint's paragraph (3), which prescribes finite-coefficient comparison for the open factor, and read Stacks `etale-cohomology.tex`, Tag 0F10 (`lemma-finite-cd`), especially assertion (1) versus assertion (2). Assertion (1) is relative and does not assume finite cd(k). I also read `proetale.tex`, Tag 09AL (`lemma-compare-constructible-derived`), and the final paragraph of Tag 09C2 (`lemma-describe-constructible-complexes`), which points out the Tor-interval comparison obligation. In the Bhatt–Scholze PDF I read Lemma 5.4.3 and Remark 5.4.4: the bounded-below limitation is essential here. There are no new node statements to review.

For step 1 I opened the statements of the qcqs-over-affine and qcqs-morphism-permanence nodes. The first explicitly includes separated finite-type schemes over a field, and the second gives both properties of the morphism from the resulting source/target hypotheses. The finite-ring arguments are written in the step: ideals and the kernel of A^r → M are finite sets; this proves the Noetherian and finite-presentation conditions without a hidden algebra lemma. The invertibility of ell^n follows from the different characteristics.

For step 2 I opened the finite-discrete internal/ordinary equivalence, constructible comparison, and Noetherian Tor-interval comparison statements. The first includes the actual unbounded derived equivalence, constant local models and each all-module interval, rather than merely an equivalence of abstract module categories. The second gives bounded étale origin. The third reflects the particular interval [a,b], so no change of bounds occurs when choosing L. A is discrete and Noetherian and U is qcqs, exactly as required. This verifies both D+ and D- hypotheses used later.

For step 3 I opened the complete statement of `det-geo-open-finiteness-ii-amplitude`: its first clause is vanishing for **all A-module sheaves**, not only underlying abelian sheaves or constructible sheaves. It applies to any field and any finite ring killed by ell^r. I checked the nonnegative-integer convention in `def-kun-cd`. Thus d_j is chosen before L or K and needs no absolute field cohomological dimension assumption.

For step 4 I read the complete `lem-sf-projection-finite-constant` statement and `lem-sf-open-tor-bound-arbitrary-field` statement. The projection theorem requires a Noetherian ring, a bounded-above input, a finitely presented constant test and the all-module direct-image bound, all supplied in steps 1–3. It gives the canonical map used by the arbitrary-field theorem, not just an unspecified isomorphism of endpoints. The latter requires a bounded-below input, the input Tor interval and finite-module projections; all are supplied, and its conclusion explicitly tests **every** étale module sheaf. I did not pass from finite constants to arbitrary sheaves by an uncited claim.

For step 5 I read the current blueprint file `sk-cor-geo-open-finiteness/cor-fin-deligne-open-finite-coefficients.md` and the corresponding DAG statement. They permit an arbitrary finite allowable ring over an arbitrary field. I verified each hypothesis against L, j, A and ell^n. This is bounded constructibility of Q itself and supplies the bounded-constructible hypothesis of step 6's interval comparison.

For step 6 I opened the ordinary pro-étale total-derived/plus-comparison node and the internal/section-module derived comparison node, in addition to re-reading the three comparisons from step 2. The former explicitly identifies the ordinary total derived direct images on bounded-below inputs and supplies the site-comparison isomorphism. The latter identifies the actual internal module-object total pushforward with the ringed section-module total pushforward; a comparison of underlying abelian sheaves alone would not suffice. Its section-action equivalence is the one used in step 2 after identifying the finite-discrete coefficient ring with the constant ring. Constructible comparison preserves bounded constructibility, and the Noetherian Tor comparison explicitly gives the interval against every pro-étale module sheaf. Finally the finite-discrete equivalence returns these properties to the original internal coefficient category. I checked that a≤b+d_j since d_j≥0. No completed or derived-adic tensor is substituted for the ordinary tensor.

For step 7 the zero-ring argument m=1m=0m=0 is written out. All its module categories are zero and d_j=0 works. The zero complex and empty U also have zero image. As a nontrivial small test, j:G_m→A^1 with constant F_ell may have nonzero boundary R^1j_*; the proof allows an upper shift d_j and never claims interval preservation without a shift. For j=id, cd(j)=0 and the original interval is retained. The argument remains valid over a non-separably-closed field, including one of infinite absolute cohomological dimension, since only relative cd(j) is used. Finite nonreduced A such as Z/ell^2 is allowed: finite test modules are finitely presented but need not have finite projective dimension; the cited projection theorem does not require that extra assumption.

I checked delivery-errors B–E against the actual files: no new statement-only-node or duplicate issue arises; every step citation has a matching statement extract in citations.json; no proof of another node is used in place of its statement; the cross-unit facts are declared as generic tools in split_report; no target statement, definition, chapter route, or unit route is changed. I checked the selected dependencies' reachable edges and found no path back to this item. All proof steps are shorter than 2000 characters; none hides an extracted comparison or all-module-test lemma. The main corrections to the initial route were to use the arbitrary-field Tor criterion, make the internal/ordinary comparison explicit, and specify the total-derived/bounded-below compatibility.

## Unfinished work

No mathematical part of this item's one-level split is left unfinished. The cited existing nodes retain their own independent stage-1/stage-3 obligations; this delivery does not claim their Lean proofs are closed. Required server dry run and push follow this report.
