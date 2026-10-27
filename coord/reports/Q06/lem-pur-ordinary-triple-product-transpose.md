# Stage-1 report: lem-pur-ordinary-triple-product-transpose

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-ordinary-triple-product-transpose.json: statement item, split in eight steps; no exact Mathlib match.
- citations.json: verbatim statements for each step/node citation.
- searches.jsonl: actual outputs logged by the prescribed msearch command.

No new nodes or Mathlib leaves. The helper prepare.py is sandbox-local and is not a delivery file.

## Attachments

None. Searched the exact blueprint tag and triple-product/transpose terminology in lean/WeilConjectures. The ProEtale finite-coefficient ExternalProduct module defines external products, and LowerStarProjection gives a binary projection-counit identity. Neither states the two specific triple composites of this item. Etale Kunneth modules concern a different site and do not attach this pro-etale statement. Existing Sheaf statements with sorry are not attachments.

## WANTED

None.

## Corrections and scope

The original item had no proof. Its full statement and statement dependencies are retained. The source path now points to literature/blueprint/latest, as required, instead of a dated snapshot. Its blueprint ancestor and via chain are retained; whole-blueprint searches for counit, external product, triple, and ordinary/product/counit found no exact alternative. The proper six-functor product and triple lemmas require properness, bounded finite-Tor inputs and a six-functor datum, so they cannot prove this arbitrary ordinary statement. In particular I did not cite their proofs as if their statements had the needed strength.

The unit sk-prop-an and the latest affine-space composition-law proof fix the purpose of this item: ordinary product reassociation beneath the integration/sign argument. The latest Kunneth coherence proof provides the counit route. This delivery establishes that finite ordinary calculation directly; it does not invoke compact-support or higher coefficients. No statement dispute was found.

## Not duplicates

No new nodes. The existing lem-pur-ordinary-derived-composite-transpose is reused rather than recreated; its normalization clause is essential. The binary two-counit identity is proved in Steps 3--5 and is not moved into another node restating the item. The small naturality and transpose expansions are explicit elementary steps.

## Review by Q06

I read delivery-errors B--E in full, the worker and stage rules, the three blueprint levels in SETUP, GOAL, the chapter and unit records, the latest affine-space composition proof (Steps 3--4), and latest lem-sf-kunneth-coherence.proof.md (clauses (i)--(ii)). The latter explains the two-counit transpose but only in the proper six-functor context; I marked this refinement agent-written and supplied the actual ordinary calculation.

For the scheme prerequisites I read Stacks schemes.tex Tag 01KU, lemma-separated-permanence, at lines 4289--4327, and morphisms.tex Tags 01T3 and 01T4, lemma-composition-finite-type and lemma-base-change-finite-type, at lines 2711--2750. For ordinary operations I read sites-cohomology.tex Tags 0D6D, 07A4, 07A6 and 0D6E (derived pullback composition, tensor comparison, adjunction, direct-image composition), and remark-base-change immediately after 0D6E. I also read Tag 0FPI's adjunction normalization statement, without treating it as a general coherence theorem by itself. The existing composite-transpose node and its cited normalization supply the exact comparison theorem.

Step 1 cites the full separated/finite-type base-change statement, finite-type composition, clause (e) of proper-fp-permanence for separated composition, and the fibre-product universal property. Each says the precise fact used; in particular no properness is inferred or assumed. The universal-property argument identifies both triple products by their maps to each Xi, including their projections. All projection and structure maps therefore satisfy the hypotheses later needed by the composite-transpose node.

Step 2 cites only the ambient finite-level clause of derived-pullback-tensor-iso, which expressly permits arbitrary unbounded inputs, is natural in both objects, and preserves associators, signed symmetry and composition. I read its whole statement, not just its title. Proetale-operations expressly supplies the ordinary unbounded Hom bijection. The two elementary transpose naturality equations follow by expanding epsilon L(h), with counit naturality, as written; no faithfulness of pullback or cohomology is used.

Step 3 cites the full definition of exchange and projection, including its explicit finite projection input a and its exchange transpose. It has the needed arbitrary unbounded P,Q domains. Transposing H gives epsilon_t L_t(E) in its first factor, which is exactly the exchange transpose in the cited statement. Tensor functoriality and naturality of the pullback-tensor comparison justify distributing the composition. This is a few-line substitution from definitions, so elementary is justified.

Step 4 expands the other binary factor Psi before cancelling any symmetry. The projection transpose is again the definition's displayed a. The finite pullback-tensor lemma carries the signed symmetry through L_v, and naturality of symmetry gives the final identity 1 tensor epsilon_v. I checked the domains: the first factor after the second swap is L_v F, the second is Q. Both swaps are degree-zero derived arrows; their composite cancels with their signed naturality, so no sign is simply suppressed.

Step 5 uses the existing ordinary-derived-composite-transpose with f=t, g=v and with the intermediate object L_v F tensor Q. Its statement expressly uses the same finite K-injective compositor as the item, and has no properness/boundedness assumptions. It therefore gives the transpose of c inverse R_v(H) Psi, not merely a transpose of some abstractly isomorphic arrow. Substitution of the two earlier formulas gives the two pulled-back counits, using the cited tensor comparison's composition law. The binary computation is smaller than the triple assertion and is fully written here; there is no hidden replacement lemma.

Step 6 applies that proved binary formula to the left outer product and precomposes it with L_v(a tensor 1). Naturality gives the explicitly displayed bracket epsilon_f12 L_f12(a), which is the transpose of the inner a. Substitution of Step 5 for this bracket gives counits 1,2,3 in order. Step 7 writes the right bracket epsilon_f23 L_f23(b) separately, yielding the same ordered counits. The two cited nodes say respectively that the canonical comparisons are natural and associative and that tensor respects composition on morphisms. These are exactly the statements taken in both steps; no constructibility of F_i or N_ij is asserted. The two reductions are elementary substitutions of Step 5, not new theorem applications left unproved. Step 8 uses the actual adjunction Hom bijection's injectivity to obtain equality of the original arrows.

I checked every citations.json quote against the corresponding current node statement: each is verbatim (the entire statement, to keep all domain clauses visible). Off-unit generic tools are declared in split_report.tool_uses for the route checker. No new node, proof sketch inside a new statement, duplicate, Mathlib leaf without a match, source-section-only reference, missing mathematical citation, or cycle is introduced. Every proof step is below 2000 characters; none conceals a separately assumed comparison or lemma. The item is not a unit key node, so no unit record changes are needed.

Edge cases checked: identity maps reduce the binary transpose to the usual tensor of counits, both of which are identities under normalization; hence both ternary products reduce to tensor reassociation. Zero inputs give zero on both sides by tensor functoriality. Empty schemes impose no pointwise or nonemptiness requirement anywhere. Odd-degree inputs retain both Koszul swaps in Step 4 and use their signed cancellation, rather than an even-degree shortcut. Inputs may be unbounded, nonconstructible and of infinite Tor amplitude; no tensor or exchange invertibility is used, and all canonical comparisons cited have the stated unbounded finite-level domains. The finite case n=1 uses the same argument and no lifting in n. I corrected the initially generated search summaries to store the actual top hits from searches.jsonl rather than an empty result field; no unexecuted query is recorded.

## Unfinished work

None for this one-level stage-1 split. Existing dependency nodes remain their owners' work. Required dry run and push results are recorded by the delivery tool.
