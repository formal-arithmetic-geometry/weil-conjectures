# Stage-1 report: lem-pur-ordinary-derived-isomorphism-transport-transpose

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-ordinary-derived-isomorphism-transport-transpose.json: item, split into five explicit steps; inherited statement, metadata and searches preserved, actual new searches appended.
- citations.json: fourteen verbatim statement excerpts, one for every step/node citation.
- report.md and the msearch-generated searches.jsonl.

New nodes: 0. New Mathlib leaves: 0. No Lean files or repository files were written, and no compiler was run.

## Attachments

None. Searched the live WeilConjectures source by exact blueprint tag, ordinary/derived transport, transposes, and the nearby right-adjoint scheme-isomorphism transport files. The latter concern scheme-module right-adjoint mates, not the stipulated unbounded pro-etale constant-module direct image and its normalized compositor. The finite-Tor etale adjunction-composition declaration also does not give the item. No exact project attachment was found.

## WANTED

None.

## Changes and issues

The statement is well typed and was retained unchanged. Its imported empty proof did not establish either the normalization-dependent transpose equation or invertibility of the actual unit. The five steps now display the compositor counit equation, its cancellation against the inverse compositor, the two naturality rewrites and the triangle identity. The invertibility argument uses existing nodes rather than creating a duplicate unit lemma or a lemma restating one of the item's clauses.

The entire DAG was searched for adjunction-composition, derived equivalences and unit/counit invertibility. Blueprint searches for adjunction, isomorphism-transport and composite adjunction, and the ancestor command, found no blueprint statement of this item. The existing derived-pullback-equivalence and adjunction-equivalence-counit nodes suffice. The item keeps same_as = []. Abstract Mathlib comp_homEquiv and triangle identities do not by themselves identify the specific derived comparison maps, so the item is not a one-line Mathlib specialization.

Generic tools from other units are declared in split_report.tool_uses: lem-sfb-ringed-derived-monoidal-comparisons supplies precisely the required normalization, and lem-weil-isomorphism-derived-pullback-equivalence supplies an equivalence on the full unbounded category. Neither changes the affine-space unit's route. The other geometric operations are already part of the item's stated setting; the counit-isomorphism node is a Mathlib leaf.

## Not duplicates

No new nodes were created. The item was compared with the existing derived equivalence, ringed-derived composition and ordinary composite-adjunction statements: they provide ingredients, not this transport formula.

## Review by Q72

I read the chapter and sk-prop-an unit records, the current main-20261015 affine-space composition-law proof (Steps 3--4), and the current lem-sf-kunneth-coherence proof's proper symmetry paragraph. The latter identifies the swapped product by taking actual adjunction transposes. The present lemma supplies the scheme-isomorphism transport calculation needed in that paragraph; it is an agent-written calculation, not a claim that Stacks states this specialized formula. I read Stacks sites-cohomology.tex, lemma-derived-pullback-composition (0D6D) and lemma-derived-pushforward-composition (0D6E), including their proofs. The latter explicitly obtains composition by the composite adjunction and uniqueness of right adjoints. I also read Mathlib Adjunction/Basic.lean's unit, counit and triangle axiom and FullyFaithful.lean's full/faithful unit argument. There are no new nodes needing additional source verification.

For Step 1 I opened every cited statement. Constant-ring composition gives the structural ring equation needed to apply the ringed comparison theorem; pro-etale pullback composition gives the particular alpha, not an unspecified isomorphism. The monoidal-comparisons statement explicitly says the canonical kappa is adjunction-compatible and explicitly gives the composite counit. Derived-direct-image-composition explicitly includes finite coefficients on all of the ordinary unbounded category. Proetale-operations supplies the actual canonical adjunction. I checked the indices: alpha is evaluated at R_q R_s E and P_c(kappa_E) precedes it, giving the correct source P_c R_c E.

For Step 2 proetale-operations gives counit naturality, and pullback-composition gives alpha's naturality. With E=P_s K', v has target R_q R_s E. Naturality at d puts d outside the transpose; the two compositor factors are adjacent and inverse. Naturality at v then has exactly the displayed target. This is an explicit calculation, not an appeal to an unnamed transport theorem.

For Step 3 the only cited node is proetale-operations, providing the actual adjunction whose counit is natural and whose unit/counit satisfy the triangle identities. Naturality is applied to eta_s:K' -> R_s P_s K'; the counit index is R_s E. The resulting epsilon_s P_s(eta_s) cancels at E=P_s K', leaving exactly the stated right side, including alpha_M.

For Step 4 I read the full statement of lem-weil-isomorphism-derived-pullback-equivalence: it applies to finite A_{E,n} and an isomorphism of schemes with ell invertible, and asserts fully faithful and essentially surjective on the unbounded pro-etale categories. These hypotheses follow from the coefficient datum and k's characteristic. The existing counit-isomorphism leaf states exactly that the counit of any specified adjunction with equivalence left adjoint is invertible. I deliberately do not cite it for unit invertibility: that is proved in the step. The triangle makes P_s(eta_s) inverse to epsilon_s; fullness lifts its inverse and faithfulness checks both composites. Thus the actual eta_s is invertible, not merely some unit of an equivalence. Functors preserve the displayed inverses, so the composite defining S_d is invertible.

For Step 5 the cited site-isomorphism statement explicitly supplies the constant-module equivalence and ring identification. The canonical unit represents its transport into R_s P_s. The cited direct-image composition statement supplies its canonical comparison on the entire finite-level unbounded category. Hence the description of S_d is its given composite; the normalization and transpose were established, rather than assumed, in Steps 1--3.

I checked B--E: no new statement-only nodes or duplicate nodes, no unsupported source tags, no changed target or hollow construction, and every proof citation has a literal excerpt in citations.json. Each step is under 2000 characters. The hypotheses never acquire properness or constructibility; no integral coefficient completion or etale/pro-etale comparison is inserted. Small cases: s=id and d=id reduce to the usual counit transpose and identity transport; q=id reduces to the triangle equation for s; zero objects and zero u give zero on both sides; arbitrary isomorphism d is handled by counit naturality without a scalar/sign choice. All formula sources and targets were checked before writing the proof.

## Unfinished work

None in the stage-1 split. Mechanical validation and direct delivery are performed with the prescribed server tools.
