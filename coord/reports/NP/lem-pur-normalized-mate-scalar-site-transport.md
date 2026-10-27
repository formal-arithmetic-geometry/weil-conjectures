# Stage-1 delivery: lem-pur-normalized-mate-scalar-site-transport

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-normalized-mate-scalar-site-transport.json: statement, split; six proof steps using existing Mathlib leaves, no new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement excerpt for each dependency of each numbered proof step.

## Attachments

None. Searched WeilConjectures for the exact blueprint identifier and for normalized mates, scalar transport, and counit/equivalence comparisons. MateCube.lean, especially CategoryTheory.mateEquiv_app_cube, proves the mate cube equation for four adjunctions, but does not state the normalized right-adjoint-model clause together with the independently specified counit-preserving transport clause. MateTransport.lean concerns a different collection of adjunctions and an isomorphism criterion. Neither is an exact attachment for every clause of this item.

## WANTED

None. The item follows the present blueprint's categorical argument, expanded by the agent; it does not rely on any SGA source.

## Corrections and limitations

The imported statement is well-typed and was preserved verbatim. Its proof was empty. The source's phrase “by uniqueness of transposes” is not itself a proof of the site/coefficient compatibility: Steps 3–5 now give the actual calculation with the specified square and both actual counits. The ancestry reaches a launcher-created seed with no blueprint ancestor; blueprint_refs.py ancestor confirms None. Kept this honest null ancestor and its existing precise place/via information, and searched the blueprint for mates, counits and transposes. There is no exact alternative blueprint statement.

The recorded inherited Mathlib searches remain in place. New searches were run with msearch.py and read: mateEquiv_counit and iterated_mateEquiv_conjugateEquiv are the relevant hits, but neither alone specializes to this whole two-part statement. Reused def-weil-pbc-adjunction-mate (mateEquiv) and lem-weil-pbc-adjunction-of-natural-bijection (Hom bijection and explicit inverse-counit formula), already Mathlib leaves. No new generic lemma or restatement of an item clause was introduced.

## Unfinished work

None in this one-level split. No Lean was written or compiled.

## Not duplicates

No new nodes. The existing eight-category equivalence-square inverse-mate coherence lemma is broader in some directions but its clause (3) goes from an already given right-square equation to a left-square equation; invoking its converse here would require an additional argument. The direct counit calculation is shorter and avoids introducing a duplicate or a disguised clause of the item.

## Review by NP

I read the current blueprint file literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, both its initial transpose paragraph and its Charts paragraph, as well as the chapter and sk-thm-purity-transport unit. This is a categorical prerequisite for that route, without changing its geometric purity construction. I read Mathlib CategoryTheory/Adjunction/Mates.lean, particularly the mate counit formulas at 123–132 and iterated mates at 450–480, and Basic.lean at 158–182. There are no new nodes needing separate source checks.

For Step 1 I opened lem-weil-pbc-adjunction-of-natural-bijection and verified its statement actually gives the inverse formula Psi^{-1}(b)=epsilon composed with F(b), not merely the existence of an adjunction. That gives the injective inverse transpose used to compare the candidate with b. The q naturality instance is on gamma_A^{-1}, from G_AK to H_AK, so the q inverse on the right is at G_AK. Expanding z cancels the right pair of gamma_A maps. Step 2 writes the inverse and obtains naturality from the given natural isomorphisms; it invokes no external theorem.

In Step 3 I checked every endpoint: after precomposing with F'_B S'(rho_A), the source is F'_B S' U_A G_AK and the target is T' V_AK. Naturality of the B counit moves G'_B(delta_Y^{-1}) to delta_Y^{-1}; the supplied B counit equation then removes rho_B. Naturality of c_B is applied to b_K itself, so its two indices are SM and G_BTK. The last equality is Step 1's actual transpose formula. Step 4 solves precisely the assumed square at M=G_AK; it uses delta_Y naturality at epsilon_A: F_AM to K. Step 5 uses the supplied A counit equation and q' naturality on rho_A, and cancels a genuine isomorphism F'_B S'(rho_A). Its two citations are read in full: the Hom-bijection statement gives uniqueness with the counit formula, and the mate definition explicitly identifies the transpose of the inverse left square. These are the exact statements quoted in citations.json.

Step 6 cites the mate definition for the globally natural transformation, not for an unstated descent theorem. Its component at an isomorphic object is written as G'_B T'(j) composed with bar b_K composed with S' G'_A(j^{-1}); global mate naturality proves that this equals the fixed component, hence independence. The given quasi-inverse supplies j for every target object. No full faithfulness theorem or choice of strict identity comparisons is needed. All intermediate expressions use functional composition, and no arrow changes direction silently.

I checked delivery-errors B–E: no new unsplit statement contains a proof sketch; no unintroduced hypotheses, implicit geometric assumptions, uncited non-elementary facts, circular use of a parent, or new nodes restating clauses occur. The algebra steps are explicitly written applications of naturality, composition and inverse cancellation. Every proof step is shorter than 2000 characters. Edge cases include empty categories, identity functors/comparisons, nonidentity natural automorphisms of identity functors, and nontrivial equivalence presentations: the formula still uses the actual counit normalization and the actual commuting square. Removing that normalization can change the mate, which is why neither equation has been discarded. The proof uses no additivity or coefficient assumption.
