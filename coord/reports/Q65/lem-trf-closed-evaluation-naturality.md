## Files written

- `dag/nodes/sec-trace-formula/lem-trf-closed-evaluation-naturality.json`: item statement unchanged; four explicit elementary proof steps; existing searches retained and five actual Q65 searches appended; status split.
- `citations.json`: one verbatim statement quotation for the one cited node in step 1.
- No new nodes and no new Mathlib leaves. Every calculation follows from hypotheses written in the item, so extracting an additional counit-naturality or hexagon lemma would create an elementary node.

## Attachments

None. The project's WeilConjectures source has no declaration with the item's blueprint tag. The related Mod.toIhomIhom, uncurryHom_toIhomIhom and its naturality lemma in CategoryTheory/Monoidal/Mod/IhomComp.lean concern internal module objects and only part of the required variance; they do not state the arbitrary closed-category result with all three arrows. They are not attachments. The project's internal-currying lemmas concern a different isomorphism.

## WANTED

None.

## Findings

The imported node had a complete statement but no proof. It needs neither dualizable objects nor invertibility of any evaluation map. Its existing monoidal-category dependency supplies precisely the tensor bifunctor and associator axioms; closedness, symmetric braiding and their naturality are explicitly assumed in the item itself. No new definition is needed.

The source read is literature/stacks-project/categories.tex, Tag 0GWJ, remark-internal-hom-monoidal, especially (1) and (5). I also read more-algebra.tex Tag 0A60, lemma-evaluate-and-more, and Tag 0A61, remark-sign-explanation. The first gives exactly the swap-then-two-evaluations construction; the latter two confirm its intended functoriality and swap normalization. The detailed categorical calculations here are an agent expansion, recorded as proof_origin.by = agent, not a claim that Stacks prints these calculations. The explanatory occurrence of hom(L,K) in the last evaluation of 0A61 is a source typo: its displayed source and target require hom(L,M). The item already has the correctly typed evaluation and requires no correction.

I read the chapter and unit records: this is a generic categorical supporting input in the inherited local-term-locality/derived-evaluation branch, not a replacement of the unit's geometric route. Its blueprint ancestry and precise inherited place are retained. Whole-DAG and blueprint searches for evaluation, iterated evaluation, closed uncurrying, two-counit, evaluation transpose and Tag 0GWJ yielded no existing node stating this full result. In particular, lem-pod-closed-uncurry-laws gives only inverse cancellation, source naturality and evaluation for the opposite tensor convention; lem-fix-monoidal-dual-hom-comparison concerns preservation of internal Hom by a strong monoidal functor on dualizable inputs; lem-sf-invertible-factor-hom-cancellation assumes an invertible tensor factor. The derived-evaluation-canonical-map node is the parent consumer of this item, not an input.

All Q65 Mathlib queries in the item were run through msearch.py and are preserved in searches.jsonl. I read the returned hits and the pinned Mathlib Closed/Basic.lean source at ev_naturality (109), curry/uncurry naturality (161–175), inverse laws (180–185), evaluation (194), precomposition/evaluation (249–254), and compTranspose/comp (387–395). The two differently phrased LeanFinder searches and LeanSearch returned these building blocks, not the full item. The Loogle query gives individual currying naturality, and the grep confirms their source locations. These individual laws here are direct substitutions in the item's explicitly assumed natural bijection; no new Mathlib leaf is required. No unavailable service was treated as a negative result. No Lean was written, compiled, or built.

## Not duplicates

No new nodes were created. The nearby existing statements above were read rather than duplicated.

## Review by Q65

I checked delivery-errors sections B–E against the node and source. There are no new-node self-containment, source, search, or duplication issues because there are no new nodes. The statement was kept verbatim and all its objects and arrows retain their original hypotheses.

Step 1 uses the statement of def-sfb-monoidal-category only for tensor bifunctoriality and its componentwise composition convention. I opened that node, checked that its statement actually supplies these, and copied the relevant sentence verbatim into citations.json. The two displayed counit laws are obtained by applying the assumed natural Hom bijection to an identity, with both transposes specified; they use neither a hidden Yoneda theorem nor an additional existence theorem.

Step 2 uses no cited theorem: existence and uniqueness are exactly the assumed bijection. I wrote out the associator-conjugated swap S and the individual braiding hexagon. Substitution cancels inverse associators and the explicit symmetric pair of braidings, leaving the required swap of B and A. Thus the left-uncurrying claim is proved by an actual structural calculation, not an appeal to unnamed coherence.

Step 3 substitutes the given u,t,v into step 1. I checked the contravariant Hom direction: h = H(u,t) has source B' and target B, whereas a = H(t,v) has source A and target A'. The two equations have sources B' tensor K and A tensor L'. This catches the possible variance error and verifies every hypothesis without an isomorphism assumption.

Step 4 uncurries both sides into arrows from (A tensor K) tensor B' to M'. I checked the two braiding-naturality equations separately, then substituted the two explicitly displayed counit equations. Both expressions become the identical displayed G. Associators are those of step 2 and are moved only using their defining naturality. Injectivity is the injectivity of the given bijection. Each substitution is elementary; no independent non-elementary subclaim is hidden in these steps. All four steps are below 2000 characters.

For small cases I checked the terminal one-object category (all identities), the tensor unit in place of each of K,L,M, and cartesian closed sets, where e(a,k)(b)=a(b(k)) and the naturality equation is v(a(t(b'(u(k))))) on both sides. In module categories this same calculation is bilinear and permits zero objects and zero arrows; no finite rank or invertibility is used. The braiding cancellation uses symmetry, which is explicitly assumed. No false statement, missing hypothesis, statement dispute, prohibited source route, off-unit theorem tool use, or unfinished proof remains.

## Unfinished work

None for this one-level stage-1 split. The mandated server dry run and direct delivery follow this report.
