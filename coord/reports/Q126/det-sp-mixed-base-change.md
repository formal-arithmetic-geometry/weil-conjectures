# det-sp-mixed-base-change — Q126

## Files written

- `dag/nodes/sec-smooth-purity/det-sp-mixed-base-change.json`: statement, marked split after auditing the existing four-step proof; no Mathlib match. Existing statement and proof retained, fresh required searches appended and split report updated.
- `citations.json`: 25 verbatim relevant statement extracts, one for every step/node citation.
- `report.md`: this report.

No new nodes; no Mathlib leaves. The initial sandbox contained no node, report or search log. I copied the current shared item, preserving its imported proof, earlier citations, searches, blueprint metadata, tool-use declarations and review history. I did not change maintainer-owned unit metadata or unit realization (the item is not the unit's key statement).

## Attachments

None. Searches by the exact blueprint tag and by mixed-coefficient/compact-support/exceptional terminology in the read-only slopmaster2 source found no project declaration stating the two identities. Upstream master was also searched as reference, never treated as proof evidence.

## WANTED

None. This is an explicit agent proof following the current blueprint's two paragraphs; no external missing document is asserted as a proof source.

## Issues found

The repository status was unsplit although an earlier substantial split and review were present. I checked the imported material rather than treating it as certified. I retained the statement, categories, coefficient hypotheses and coefficient-independent compactification. The proof uses ordinary uncompleted constant-ring module categories throughout, not condensed coefficients or completion.

The isomorphism arrow on exceptional base change is inherited notation, as the prior maintainer review observes. This item uses its transpose definition only and proves its compatibility; its invertibility is not used in any calculation here. Only compact-support base change and coefficient comparison are inverted.

## Unfinished

Nothing required for this stage-1 split. Dependencies retain their own stages; this delivery asserts no Lean proof.

## Review by Q126

I read the current main-20261015 mixed statement and both proof paragraphs, the chapter and sk-prop-sp-purity-bc unit. The unit needs the finite-level mixed identities to assemble compatible tower maps. The proof stays on exactly that route: compactification, open and proper factors, then adjunction. I opened every cited node and checked the clauses quoted in citations.json. No SGA source is used.

Step 1 uses def-cbc-compact-support-square for the pulled-back compactification and lem-sbc-smooth-relative-dimension-permanence (1) for the relative dimension of f'. The scalar-extension definition gives the target-ring action and K-flat computation; prop-weil-pbc-proetale-constant-ring-map gives the constant-ring isomorphisms. The derived tensor/pullback lemma explicitly preserves flat K-flat representatives. Together with lem-pc-kflat-resolution and the exact pullback/derived adjunctions of def-weil-pbc-proetale-operations, these justify the local tensor computation and its compatibility with the square isomorphism. This is not an appeal to morphism detection by geometric stalks.

Step 2 uses the proper comparison's definition in det-sp-reduction-direct-image and the precise counit-transpose formula and bijection in def-weil-pbc-adjunction-mate. I recomputed both transposes: naturality of theta moves the pullback of gamma before its counit equation; the other transpose uses gamma' followed by the defining equation of q_A. Both give extended scalars of the same pulled-back counit. The statement of the cited direct-image node specifies this normalization, not merely existence of an isomorphism.

Step 3 uses the actual canonical open base-change map of lem-cbc-proetale-extension-zero-base-change, the sheaf tensor identity of lem-weil-pbc-ringed-slice-extension-tensor, exactness and adjunction of lem-cbc-proetale-extension-zero, and the defining presheaf of def-weil-extension-by-zero. Flatness of j_!P follows by writing tensor with it as j_!(P tensor j^*(-)); K-flatness follows by the identical calculation on an acyclic complex. Preservation of sums follows directly from the displayed left adjunction. Restricting the two mixed open maps gives the identity; the unit of the open adjunction is the identity from its explicit restriction, so its Hom bijection makes restriction injective on maps from j'_!. These are elementary deductions of the cited statements, not an uncited general base-change theorem. The termwise open comparison is justified by exactness.

For the compactification formula, def-cbc-exchange-map states precisely the proper-exchange-then-open-exchange composite. thm-cbc-finite-level-proetale is used only on etale-origin inputs. Its hypothesis is supplied for arbitrary finite rings by lem-weil-pbc-finite-ring-constructible-derived-origin, for M_B by clause 2 of det-sp-scalar-extension-functor, and for j_! by the termwise isomorphism of lem-cbc-proetale-extension-zero-comparison. The proper maps p and p' are qcqs, so lem-weil-pbc-transport-identifies-exchange applies and identifies the transported exchange with the actual pro-etale counit mate. I checked all five lines of the assembly: naturality of q_B at E must precede Step 2, and naturality of gamma' at a_A gives the fourth line. This proves the first identity with the specified maps, not just isomorphisms of their objects.

Step 4 uses the constructible adjunction and the exact defining counit equation for c in det-sp-reduction-exceptional, naturality of b in det-sp-reduction-direct-image, and the adjunction bijection of def-weil-pbc-adjunction-mate. N=f_A^!K is in the finite-Tor constructible category by that cited adjunction. The two transposes end in inverse composites in opposite written orders; inversion of the first identity at N identifies exactly those factors. I verified sources and targets and did not invert e.

I examined every non-elementary step over 2000 characters. The open part of Step 3 is the short tensor/exactness and adjunction deduction just described, and its remaining long portion is the explicit five-line assembly; it does not hide a non-elementary lemma. Step 4 is one counit/naturality calculation with both sides displayed. No clause was merely moved to a new node, and no new node or duplicate was created. Existing off-unit statements are generic tools and their split_report declarations were retained.

Edge cases checked: identity A to A and v=id give identity squares; zero M or K and empty schemes give unique maps; B=0 also gives the zero category; d=0 causes no shift issue; the nonflat map Z/ell^2 to Z/ell uses K-flat derived tensor, so no underived tensor or flatness of B is presumed. There is no statement dispute or change of hypotheses.

I ran all four prescribed search kinds and a second semantic/mate phrasing, and read their actual results. Generic mateEquiv_counit and mateEquiv_vcomp at Mathlib/CategoryTheory/Adjunction/Mates.lean:123,170 were read: they support the existing abstract mate node but do not themselves state these pro-etale mixed identities. Algebraic tensor base-change and underived sheaf pullback hits are likewise not this item. The exact current query texts and outcomes are appended to the node and retained in searches.jsonl.
