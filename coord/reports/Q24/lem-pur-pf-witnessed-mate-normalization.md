# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-pf-witnessed-mate-normalization.json`: statement item, now split in four steps. Statement and statement dependencies retained verbatim. Mathlib verdict: no match after two semantic phrasings, Loogle, source grep, and LeanSearch. Existing historical searches are retained; the five fresh searches and actual hit lists are appended from `searches.jsonl`.
- `citations.json`: one verbatim statement quotation for each step/node citation.

No new nodes and no Mathlib leaves. No Lean files, compiles, repository edits, or direct git operations.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint tag, properOpen/proper_open, proper/open, clopen projector and mate terminology found no declaration proving every clause. General projection-mate declarations in `CategoryTheory/Adjunction/ProjectionMapMate.lean` do not construct the specified geometric comparisons.

## WANTED

None. The current blueprint, Stacks sources, and existing finite normalization statements suffice.

## Problems found and repaired

The item had no proof. The important issue is that an isomorphism of endpoints does not identify the particular proper/open map with the counit-normalized mate. The proof now first proves the same four-factor formula for both named maps, then explicitly cancels the open comparison and the witness.

The source field retains its historical snapshot, as required. I read the current `literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`: its compactification-independence sentence is still the source of this normalization obligation. I also read the current ancestor `sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md`; its Step 4 is now just the block-permutation conclusion and no longer explicitly mentions compactifications. The existing `blueprint.from` records the historical extraction chain, which I retain. This is a provenance difference, not a false mathematical statement or a reason to change the chapter/unit route. The finite normalization tool supports the existing affine-space route without invoking an abstract six-functor axiom.

No new elementary facts, specializations, or clauses were promoted to nodes. In particular `lem-cbc-finite-clopen-mate-site-transport`, created for `lem-cbc-strict-tower-proper-open-calculus`, already supplies the general finite clopen comparison needed here. Reusing that existing sublemma avoids a duplicate tower-evaluation or finite-site normalization node.

## Not duplicates

No new nodes. The whole-DAG searches for `0F7B`, clopen, proper/open, evaluation and constant-tower normalization and `tools/blueprint_refs.py search` for `proper/open`, `constant-tower`, `clopen`, and `witness` were read. Nearby blueprint results concerning base change, clopen section restriction, or the existence of a proper/open isomorphism do not state this full witnessed equality. The general finite-site transport theorem is reused rather than restated.

## What remains unfinished

Nothing at stage 1: all non-elementary inputs are existing statement nodes. Their future Lean proofs are outside this delivery.

## Review by Q24

I checked the item against the current blueprint projection-coherence proof, the current affine-space composition proof, and the chapter/unit records `sec-smooth-purity` and `sk-prop-an`. I read Stacks `more-etale.tex`, Tag 0F7B (`lemma-shriek-proper-and-open`), including its first proof paragraph: the etale comparison is the ordinary proper/open identification followed by an injective-resolution arrow. I read `proetale.tex`, Tag 09AF (`lemma-jshriek-comparison`): the open comparison is the adjoint comparison, not a chosen endpoint identification. The source does not by itself assert the extra pro-etale clopen-mate equality; the proof therefore cites the existing agent-formulated finite transport theorem for that equality. There are no new nodes whose source or hypotheses need a separate review.

Step 1 uses part (a) of `def-sf-refinement-comparison-isomorphism` for the actual witness-conjugation formula and for the finite-type compactification schemes being Noetherian. Its field, coefficient and refinement hypotheses match the item's with K0=k. The finite transport theorem explicitly says that L and k!L stay in its bounded-below comparison domains, which is exactly what this step takes from it. I did not infer that a bounded-below tensor is automatically bounded below. The item separately supplies a witness and lower bound whenever such an input is used.

Step 2 uses the statement of `lem-cbc-finite-clopen-mate-site-transport`, the finite-site sublemma of the constant strict-tower calculus, with (V,W,S,T)=(X,Xbar1,X,Xbar2), (k,i,r,p)=(j1,j2,id,v). It permits a noncartesian square, so no false assertion that a refinement square is cartesian is made. Its alpha uses exactly the cartesian-open comparison followed by the clopen identity/zero projector. The statement of `lem-sf-proper-open-projection-mate` defines its gamma as the proper mate of this same alpha. Thus the gamma in the transport equation is the item's gamma. The canonical-mate comparison statement gives the displayed counit equation for b; at the identity edge it reduces to b_id=1 under the canonical identity identifications. Substituting r=id in the transport equation removes J2(b_id), leaving the stated three factors followed by inverse e_j2. All rings are finite; H has a lower bound; the opens are quasi-compact as in the item; properness implies the needed qcqs conditions already built into the finite theorem. I checked all directions of e and b: both routes start at nu* j2! H and end at Rv* J1 nu*H.

Step 3 uses the exact refinement clause in `lem-cbc-proper-open-interchange-coherence`: when A=C and r=id its map is alpha_u of the specified etale construction. The normalization node `lem-sf-proper-open-comparison-site-normalization` states the equality alpha_p e_j2 = Rv*(e_j1) b_v nu*(alpha_e). Comparing that with Step 2 and cancelling the invertible e_j2 proves equality of actual maps. Neither node is cited merely for the existence of an isomorphism, nor is a hidden construction taken from its proof.

Step 4 is elementary naturality and cancellation: gamma is the natural proper-adjunction mate already specified in the projection-mate statement. I wrote S(a) gamma_K = gamma_M J2(a) before cancelling J2(a). The same naturality equation at any underlying arrow t gives naturality on the witnessed category and independence of the witness. The argument for a tensor input is a separate application to that input with its supplied witness; it does not assume a tensor equivalence or constructibility theorem. No new geometric or tensor lemma is hidden here.

I tested the identities for zero H/M, empty X, identity refinement and a refinement with a nonempty extra clopen component over the open. The component is projected away, not identified with all of the inverse-image open. An empty complementary component makes the projector the identity. A different witness a changes the conjugated expression by exactly the naturality relation written in Step 4. These checks preserve all hypotheses and all clauses of the original statement.

For B–E: there are no new statements, hollow definitions, new Mathlib leaves, or new source tags. Every uses-entry is backed by a verbatim quotation in citations.json; the quoted formulas are the ones used above. All six off-unit tools are declared in split_report.tool_uses with their precise purposes. No new step exceeds 1000 characters, so no non-elementary step reaches the 2000-character long-step threshold. No SGA source is used. The only correction during self-review was to use the existing finite transport sublemma, instead of adding an unnecessary constant-tower specialization node.

The first dry run flagged the context-dependent phrase “the item's explicit four-factor formula” (B2); I replaced it with “the explicit four-factor formula in the statement”. The mathematical objects and hypotheses were already introduced explicitly.
