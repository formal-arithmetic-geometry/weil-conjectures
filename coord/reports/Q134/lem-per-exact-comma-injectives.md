# Stage-1 delivery: lem-per-exact-comma-injectives

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-exact-comma-injectives.json`: existing statement node, now split into nine complete proof steps. Statement unchanged. Not a Mathlib leaf: the searches find only generic exact-functor, adjunction, enough-injective, and reflective-transfer tools, not the comma construction with all the asserted clauses.
- `citations.json`: one entry for every citation of every step, with a verbatim statement quotation.
- `searches.jsonl`: six actual searches by the required msearch command. The existing node's inherited searches are retained; the six new records are appended to its search history.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit, chapter, Lean, or live project file is changed. All five cited nodes already exist as Mathlib leaves.

## Attachments

None. Searched the slopmaster2 `WeilConjectures/` source for the exact blueprint id and for comma/injective/abelian combinations, and read the category-theory comma directories. There is no declaration stating the entire item. The existing spectral-sequence file refers to the generic right-adjoint/injectivity result but does not construct this comma category. No master sorry declaration is treated as a finished proof.

## WANTED

None. The source material needed for this split is present locally.

## Findings and corrections

The statement is true as given; no STATEMENT-DISPUTED correction is needed. The original node had a statement but no proof. Its source field correctly distinguishes the Stacks adjunction ingredient from the agent auxiliary construction; that distinction is retained, with `proof_origin.by = agent`.

I read ILO, Exposé XVI, printed p.248 (PDF page 254), the relative-cohomology paragraph immediately before Lemma 3.4.9. It asserts a triangulated relative cohomology functor but does not state this exact-comma lemma. The parent node `lem-per-kummer-relative-cone-functor`, Step 4, uses the comma lemma to construct simultaneous injective resolutions. This delivery fills precisely that auxiliary gap; it does not claim that the construction is a verbatim ILO result. I also read the chapter and unit records and the current main-20261015 ancestor proof. The existing blueprint ancestry refers to a historical regular-coefficient input, whereas the current ancestor proof uses perverse adjunction bounds. The historical provenance is retained and made explicit in the split report; the unit or current ancestor route is not changed or replaced.

The proof does not assume that $R$ is exact, that $RJ$ is injective, that $L$ preserves injectives, or that the counit is monic or epic. These would be unnecessary and potentially false extra assumptions. Instead the objects $(I,0,0)$ and $(RJ,J,\varepsilon_J)$ are injective **in the comma category**, since they are right-adjoint images under the exact evaluations. The graph and zero-section functors are the exact left adjoints needed to deduce injectivity of both components of an arbitrary injective triple.

During source checking I corrected the initially drafted tag numbers against `literature/stacks-project/tags/tags`: kernel/cokernel definitions are 0106, the kernel-mono lemma is 0E43, the zero-kernel/mono characterization is 010C, and injective objects are 0135. The proof uses the actual statements, not remembered section numbers.

## Unfinished work

None in this one-level split. The nine arguments prove every clause of the item using existing Mathlib leaves; no new unsplit prerequisite is needed.

## Not duplicates

No new nodes were created. Searches of the whole DAG and blueprint for comma categories, injective evaluations, and generic adjoint preservation found no equivalent blueprint theorem. The imported blueprint search for “comma” returned zero nodes. The generic statements about preservation of colimits and injective objects already have nodes, which are cited rather than duplicated.

## Mathlib research

Ran leanfinder with two phrasings of this exact-comma theorem, loogle with `CategoryTheory.Comma, CategoryTheory.Abelian`, leansearch for abelian comma categories and enough injectives, and two grep searches of the category-theory source. Every query and the returned digest is in `searches.jsonl`; no unavailable service was reported. Read the comma-related grep hits in `Abelian/GrothendieckAxioms/Sheaf.lean:81` and `Abelian/Pseudoelements.lean:9`: they are an essentially-small-site hypothesis and an import, respectively. Read `Abelian/Transfer.lean:95` (`abelianOfAdjunction`): it requires an adjunction exhibiting a reflective subcategory and is not the comma theorem. Read `ShortComplex/ExactFunctor.lean`, including the exact-functor equivalences described in its module documentation: these do not supply the comma structure or the four adjunctions. The other semantic hits concern injective resolutions in an already abelian category or Grothendieck categories with additional hypotheses. None specializes to the full item in one line.

Read the existing generic Mathlib matches, especially `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms` in `Preadditive/Injective/Preserves.lean:49`, `Injective` and `EnoughInjectives` in `Preadditive/Injective/Basic.lean:32,64`, and `Adjunction.leftAdjoint_preservesColimits` in `Adjunction/Limits.lean:92`. Their DAG statements cover exactly the uses below. All five cited nodes are already Mathlib leaves, so there is no off-unit statement-tool declaration to add.

## Review by Q134

I checked delivery-errors B–E against the actual node statements, the Stacks text, and the source-code hits. No new statement, hidden lemma node, elementary duplicate, or copied clause is introduced. The item statement and its two statement dependencies are unchanged; enough injectives and exactness are already explained inline. The proof dependencies are exactly the union of step citations. The blueprint `from.place` was already specific and is retained, and `same_as` is the empty result of the global search.

For the item I read Homology 00ZY (`definition-preadditive`), 0106 (`definition-kernel`), 0109 (`definition-abelian-category`), 0E43 (`lemma-kernel-mono`), 010C (`lemma-characterize-injective`), 010E (`definition-exact`), 0135 (`definition-injective`), 0137 (`lemma-product-injectives`), 0138 (`definition-enough-injectives`), and especially 015Z (`lemma-adjoint-preserve-injectives`), together with Categories 0038 (`lemma-adjoint-exact`). The product-injectives text omits its proof; the needed two-factor case is proved directly in Step 9, rather than silently importing the omitted argument. There are no new nodes whose sources would need separate checking.

1. Step 1 uses `def-sp-abelian` for the preadditive structure, zero objects and biproducts in the two categories. I checked that its statement gives these data. The formula for the structure map on a biproduct verifies the inclusion/projection equations directly using additivity of $L$, so no separate theorem about comma biproducts is hidden. The zero-object assertion follows from the displayed identity calculation.

2. Step 2 uses `def-sp-abelian` for component kernels. The factorization into the kernel of $b$ is justified by $buL(k_a)=0$, and the factorization of any test morphism is a morphism of triples because composing its required equation with the monic kernel arrow gives the known original equation. Thus this is a complete universal-property verification, not a claim that arbitrary comma projections preserve kernels.

3. Step 3 uses `def-sp-abelian` for component cokernels and `lem-weil-pbc-left-adjoint-preserves-colimits` for preservation of the cokernel by $L$. I opened the latter node and verified that its statement gives preservation of a specified colimit for a small diagram. The parallel pair $(a,0)$ has a finite indexing category, so its size hypothesis is met. Additivity preserves the zero arrow. Both existence of the induced structure map and uniqueness/compatibility of test factorizations are written out. Cancellation uses the fact that $L(q_a)$ is itself a cokernel, not a claim that an arbitrary functor preserves epimorphisms.

4. Step 4 cites `def-sp-abelian`; the mono/zero-kernel test is proved inline by factoring differences, and the epi test is its explicit opposite-category version. Because a triple is zero exactly when its identity has two zero components, the component criterion follows from the universal properties in Steps 2–3. This uses no unproved component-detection theorem.

5. Step 5 cites `def-sp-abelian` specifically for its normal-mono and normal-epi axioms, which its statement actually includes. I checked the short argument that a kernel of some map is the kernel of its own cokernel, and wrote its epi counterpart too. Together with the constructed component kernels/cokernels this verifies those very axioms in the comma category. Thus no coimage/image comparison theorem, nor an abelianness theorem with missing hypotheses, is being smuggled in.

6. Step 6 cites `def-sp-abelian` and uses the already proved universal properties to test short exact sequences in components. Both implications are included. Its conclusion about $\Delta$ uses exactly the assumed preservation of short exact sequences by $L$; no equivalence with finite-limit exactness is needed. The auxiliary zero-section is exact because its components are zero and the given sequence. These are elementary applications of the definition, with all formulas stated.

7. Step 7 cites `lem-sp-right-adjoint-preserves-injectives`. I opened its statement: it concerns an exact functor between abelian categories and its right adjoint, exactly what is available here after Steps 5–6. The natural Hom bijections establish $\Delta\dashv e_0$ and $Z\dashv e_1$ with the correct orientation. Hence the cited conclusion gives injectivity of the two evaluated components. No enough-injectives hypothesis is required for this implication of 015Z.

8. Step 8 uses the same cited statement, now for the adjunctions $e_0\dashv r_0$ and $e_1\dashv r_1$. The displayed Hom descriptions, counit relation and transpose uniqueness check their orientation and naturality. The right adjoints are additive, since $R$ is additive, and their left adjoints are exact by Step 6. The statement really gives injectivity of these images in the comma category, which is all the next step requires.

9. Step 9 cites `def-sp-enough-injectives` for choosing the two monomorphisms, and `def-sp-injective-resolutions` for its first sentence, the injective lifting property (not for existence of resolutions). I opened both nodes and copied those statements into `citations.json`. The pairing has second component $j$ and first component with projection $i$, so it is monic by Step 4. The finite biproduct target is injective by separately extending its two projections and pairing them. This is two applications of the cited definition, not an unsupported invocation of a product theorem. This completes the conclusion rather than moving it to a newly named node.

I tested the construction on $L=\mathrm{id}$ (ordinary arrow category), $L=0$ with zero right adjoint (the product category), zero source or target objects, and the trivial component categories. For an arrow $P\to N$ the injective envelope target is $(I\oplus J\to J)$ with projection, and the embedding is $((i,ju),j)$; it has both required monic components. For $L=0$ the target reduces to the independent injective embeddings into $I$ and $J$. In the general case, $\varepsilon_JL(\widehat{ju})=ju$ checks the defining square of the embedding, even when $R$ is not exact. These checks do not expose any missing hypothesis. All steps are below 2000 characters; none hides a separate comparison lemma or an unspecified standard argument.

The server `review_split` check passed: 0 new nodes, proof written by an agent. The required full delivery dry run follows this report; only a successful push counts as delivery.
