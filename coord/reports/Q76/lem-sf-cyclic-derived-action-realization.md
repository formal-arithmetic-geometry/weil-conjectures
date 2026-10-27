# Q76: lem-sf-cyclic-derived-action-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-cyclic-derived-action-realization.json`: statement, split; no exact Mathlib match. Seven explicit proof steps, reusing existing nodes throughout.
- `citations.json`: one verbatim statement quotation for every node used in every step.
- `report.md`: this report.
- `searches.jsonl`: the unmodified records written by the required Mathlib search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches in the live `lean/WeilConjectures/` for the blueprint tag, cyclic actions, strictification, rectification and mapping telescopes found no declaration proving this item. Other rectification declarations concern homotopy squares or site systems and do not state this theorem. Source declarations containing `sorry` have not been treated as finished proofs.

## WANTED

None. The original strictification argument below is explicitly marked `proof_origin.by = agent`; I do not attribute it to a missing textbook or pretend that the blueprint proves it.

## Original node and blueprint

The item had a self-contained statement but no proof. Its statement is retained verbatim, including the exact equation, the cohomology interval, the arbitrary isomorphism-invariant class, and the disclaimer about functoriality. No statement dispute was found.

I read the chapter record, the unit `sk-prop-sf-biduality-general`, and the current `cor-coef-verdier-weil-equivariance.proof.md`. The unit's geometric biduality route is not replaced. This is the native-derived realization obligation introduced below it, not a new geometric input. The supplied source ends by asserting the exceptional-adjunction comparison through the same units and counits; it does not prove essential surjectivity of realization. The proof here therefore records an agent construction. The inherited created-item ancestry has no imported blueprint ancestor: `blueprint_refs.py ancestor` reports `None`. I retained that null ancestry and made `from.place` name the precise sentence and the obligation it supplies. Whole-blueprint searches for `cyclic`, `strictification`, and `realiz` found no blueprint theorem that states this realization.

I searched the whole DAG by K-injectivity, exact filtered colimits, homology and fixed pairs before writing. The general exact-colimit theorem already exists as `src-weil-homology-preserves-exact-colimits`; the nearby directed-colimit theorem is only for abelian groups and the nearby filtered cochain theorem only for modules over a commutative ring. Neither was used in place of the general theorem. No new node was needed.

Mathlib searches were run only through `msearch.py`. Both semantic phrasings were read: derived localization, bounded truncation, and exact induced functor results do not strictify an invertible derived action. The grep hits in `CategoryTheory/Limits/Shapes/SingleObj.lean` (lines 62 and 70) are fixed-point descriptions of limits of sets, not realization in derived categories. I read these declarations, `DerivedCategory.isIso_Q_map_iff_quasiIso` at Basic.lean:298, and the exact-functor localization factorization at Localization.lean:375. Earlier searches recorded in the imported item are retained, with six additional searches backed by this sandbox's log. All services answered successfully.

## Unfinished work

None at the requested one-level split. No Lean source was written or compiler/build invoked. The only files I wrote are in the assigned sandbox. No repository git command was run.

## Not duplicates

No new nodes. Existing fixed-pair forgetting, K-injective resolution, K-injective Hom, equivalence-preserves-colimits and exact-colimit homology nodes are reused; the proof does not introduce aliases for the item or its clauses.

## Review by Q76

I read delivery-errors B through E, including the second copy, with the actual item, sources and dependency statements open. There are no new statements to audit under B, and the item's statement needs no correction. The source material read for the actual construction was the current blueprint's final exceptional-adjunction sentence; that sentence leaves this obligation open. For the input theorems I read Stacks `injectives.tex`, Tag 079P (`theorem-K-injective-embedding-grothendieck`), `derived.tex`, Tag 070I (`lemma-K-injective`), and `injectives.tex`, Tag 079B (`definition-grothendieck-conditions`). I also read the exact-colimit homology proof in `lean/WeilConjectures/CategoryTheory/DerivedCategory/DegreewiseLimits.lean`, lines 76-89 and 142-144. The sequential-colimit construction and its compatibility calculation are mine and are identified as such.

Step 1 uses the *statement* of `lem-sf-fixed-pair-derived-forget-comparison` for abelianness, exactness and conservativity, specializing all its auxiliary data to identities as indicated. It uses `lem-sfb-grothendieck-k-injective` for a K-injective target, `lem-weil-pbc-kinjective-hom-derived` for the Hom bijection into that target, and `lem-weil-pbc-exact-functor-derived-factorization` for the termwise image of P. Those nodes say precisely these things. The source of the map need not be K-injective, and the chosen representative f need not have a strict chain inverse. Invertibility of Q(f) implies that the homology maps of f are invertible by the definition of the derived cohomology functors, not by an unmentioned enhancement theorem.

Step 2 uses `lem-galois-equivalence-preserves-limits` for kernels, cokernels and colimits of an equivalence, the exact-functor factorization for preserving quasi-isomorphisms, `def-sp-grothendieck-abelian` for existence of the countable colimits, and `def-weil-pbc-category-colimit` for their universal property. The quasi-inverse has a unit and counit satisfying triangle identities; the formulas keep them rather than treating P and its inverse as strictly inverse. The diagram is indexed by the nonempty directed poset N, so no large-index or nonfiltered colimit is being used. The differential and its square follow on cocone legs, as written.

Step 3 uses the general statement `src-weil-homology-preserves-exact-colimits`, not a sheaf-specific or module-specific version. Its hypotheses hold because the ambient abelian category has exact filtered colimits and N is small and filtered. The comparison carries the actual cocone legs, as the preservation assertion means; I checked its implementation in DegreewiseLimits.lean. The inverse to the initial leg is written out using the inverse transition composites, so there is no unstated theorem about a homotopy colimit. This is an ordinary degreewise filtered colimit.

Step 4 uses `lem-galois-equivalence-preserves-limits` to make P(C) the colimit of P(X_n), and the colimit definition to define the chain map tau. I checked the special initial compatibility separately: epsilon_0 P(g_0)=f uses the triangle identity. At positive indices, epsilon_(n+1) P(g_(n+1))=g_n epsilon_n is the naturality square of the counit. Those identities give exactly the two cocone equations in the step. No coherence/strictification lemma is hidden here: this is the explicit core construction of the item.

Step 5 uses the already specified colimit universal properties and the actual definition of a fixed-pair morphism. The inverse cocone has components P(j_(n+1)) epsilon_n^{-1}; I checked its transition equality and both inverse equations on all legs. The n=0 leg of P(C) is covered by P(j_0)=P(j_1)P(g_0), so a cofinality assertion has not been substituted for a proof. The differential is a fixed-pair morphism because tau is a chain map. I marked this verification elementary, since every equality is an inverse/naturality substitution followed by uniqueness, with the formulas all present.

Step 6 uses exact termwise derivation from `lem-weil-pbc-exact-functor-derived-factorization`. The chosen e is a Q(j_0)^{-1}; multiplying the actual chain-map equality and cancelling D(P)(Q(j_0)) gives exactly e theta_M = v D(P)(e). This checks the specified derived isomorphism, not merely the action it induces on cohomology. The termwise factorization identifies theta_M with Q(tau), so the square is correctly typed.

Step 7 uses exactness and conservativity from the existing fixed-pair forgetting theorem and the kernel/image formula in `def-weil-abstract-derived-category`. Exactness gives U H^q(M) isomorphic to H^q(N). Conservativity reflects the isomorphism from zero whenever this vanishes, proving the same cohomology interval. Membership in S is then transport along an isomorphism; no closure of S under infinite colimits is assumed. This is the final elementary consequence of the displayed cohomology isomorphism.

For E's edge-case audit, N=0 gives an acyclic output, and works even if a representative of the invertible derived morphism is the zero map of a nonzero acyclic complex: no chain inverse is used. For P=id and I concentrated in degree zero, the construction reduces to the direct limit of an invertible endomorphism and tau is the prescribed endomorphism, with the direction of the square as stated. A nonidentity equivalence (for example swapping the factors of Ab x Ab) still satisfies the counit identities used above, so the proof has not silently assumed P=id. Arbitrary cohomology intervals and arbitrary isomorphism-invariant S are respected through the actual cohomology isomorphisms, including degrees where both sides vanish.

I checked C1/C4 for every use by reading each quoted dependency statement; `citations.json` contains a verbatim part (the full statement) for each such use. Non-elementary resolution, exact-colimit and exact-derived facts all have cited nodes. The two universal-property verification steps do not hide a new lemma with independent hypotheses. All seven steps are shorter than 2000 characters. I checked that no chosen proof or statement dependency reaches the item, so there is no circular dependence on realization through the fixed-pair theorem. Off-unit generic tools are declared in `split_report.tool_uses`, without setting the maintainer-owned `tool_uses` field. The split proves the item by a concrete construction and does not move any clause into a new node.
