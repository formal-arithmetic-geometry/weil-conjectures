# Stage-1 delivery: lem-trf-derived-transpose-comparison-unit

## Files written

- dag/nodes/sec-trace-formula/lem-trf-derived-transpose-comparison-unit.json: existing statement, now split in three steps; not a Mathlib leaf.
- citations.json: four verbatim statement excerpts, one for every step/node citation.
- searches.jsonl: actual Q50 searches of the item. No new nodes and no new Mathlib leaves.

## Attachments

None. I searched the blueprint tag and the notions in lean/WeilConjectures/. CategoryTheory.NatTrans.mapHomotopyCategoryPlus_mateEquiv_app (HomotopyCategory/Adjunction.lean:604) proves the first clause only. CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac (RightDerivedFunctor/PlusAdjunction.lean:419) instead states a comparison for a specified derived square with a separate hθ hypothesis. Neither gives every clause of this item under only its hypotheses. No exact tagged declaration was found. No compiler was run.

## WANTED

None. The source files needed for this formal calculation are present locally.

## Problems found and changes

The item was unsplit with no proof and no sandbox continuation. Its statement is well typed and is unchanged. The real missing argument is the use of naturality of the comparison map at d, after the primed unit normalization. This avoids assuming that H(P) is injective or that its comparison is invertible. No statement dispute or source error was found. No statement dependencies were added or removed. Earlier Q70 Mathlib search records are retained as inherited history; fresh Q50 searches were run through msearch.py and appended with their actual results.

Read the current latest blueprint chapter, unit, and lem-trf-local-term-locality statement and proof. This is the generic mate calculation inside the existing normal-cone descent comparison route, not a replacement of the trace-formula unit argument. The blueprint ancestor and its precise extraction place are retained. Blueprint searches for transpose, mate, termwise, and derived transpose found no imported blueprint statement of this exact pair of identities. The last of these returned no hits. Reuse the already existing mate definition, termwise adjunction, normalized derived adjunction, and natural comparison theorem. Do not create a new node for any of the three elementary substitutions.

## Not duplicates

No new nodes, so no new/existing same-tag pairs.

## Review by Q50

I read delivery-errors B–E in full (including the copied new-target version). The proof has 1344 characters in total; every step is below 2000 characters. It contains no hidden construction or standard comparison lemma: step 1 is a component calculation, step 2 is an instance of a quoted unit identity, and step 3 is the defining naturality equation and functoriality of q. Nothing is moved to a restatement node.

For the item I read PlusAdjunction.lean:410–466, especially the hypotheses of derivedPlus_mateEquiv_app_fac and its h₅/h₆ naturality and unit equations, and HomotopyCategory/Adjunction.lean:599–648. I also read derivedPlus and its normalization equations at lines 129–160. The source proves a larger result involving a derived square; the three steps extract only the part needed here and spell out its argument. Proof origin is agent, with those exact read-only project sources named.

For step 1 I opened the statements of lem-weil-pbc-termwise-adjunction-homotopy and def-weil-pbc-adjunction-mate. The former explicitly gives the termwise chain-map unit/counit, their homotopy classes, and bounded-below restriction (clauses (a)–(c)). The latter gives exactly the three-arrow mate formula. Additive abelian categories meet the former's additive-category hypotheses; R, R′ and the left adjoints are specified additive. Naturality of σ makes its degreewise maps chain maps, since σ at each differential is precisely the chain-map equation. Expanding d and applying functoriality gives the displayed ordinary component of b, hence equality of actual chain maps before taking classes. No chain-level identity is deduced merely from equality in a quotient.

For step 2 I opened lem-trf-bounded-below-derived-adjunction. Its statement includes the exact unit identity used, with the direction of φ from D(L)(qM) to qK(L)M. Substituting L′, R′ and M is legitimate: A′ has enough injectives and L′ is exact. It requires no enough-injectives assumption on B′. The arrow U′(φ) composed with η′ has target U′(qK(L′)M), so postcomposition by U′(q(d)) is typed. The declared normalization in the item is exactly that of the cited node.

For step 3 I opened lem-weil-pbc-right-derived-plus-injective. Clause (1) supplies α′ as a natural transformation on every object of K⁺(A′), not just injective complexes. Both K(L′)M and W are bounded below: termwise additive functors preserve the zero terms, and all compositions use finitely many such functors. Its naturality equation has domain qK(R′)K(L′)M and codomain U′(qW), as required. The final substitution uses the equality already proved in step 1. The only remaining facts are composition associativity and q(f ∘ g) = q(f) ∘ q(g). The two off-unit generic inputs are declared in split_report.tool_uses; the normalized derived adjunction is already in this unit.

I checked sources of those inputs where relevant: Stacks derived.tex, Tag 08BJ (lemma-adjoint-preserve-K-injectives), explicitly uses the homotopy adjunction; Tag 05TI (lemma-enough-injectives-right-derived) gives the everywhere-defined bounded-below functor; sites-cohomology.tex, Tag 07A7 (remark-base-change), constructs base change by transposing the counit. None is used to claim an additional uncited theorem; the exact input statements above carry the needed facts. No SGA source is used.

I tested zero P, zero σ, identity functors with identity adjunction, a complex concentrated in one degree, and arbitrary noninjective W. The first three reduce to zero or identity compositions. In one degree the first clause is the ordinary mate formula. The last case still uses naturality only, so no erroneous invertibility restriction appears. The argument also never divides by or cancels any map. All cited statement excerpts were checked literally and saved in citations.json. No unsupported definition citation, cycle-inducing new edge, hollow construction, or changed target occurs.

Mathlib queries were run for the item using leanfinder (two different phrasings), loogle, leansearch, and grep (two patterns). I read the hits and the derivedη_fac_app source in Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:91–109. The hits are the generic unit/counit comparison formulas and naturality facts; none states this combined termwise/derived mate result under the stated bounded-below hypotheses. The specialized Plus mate names have no Mathlib grep hits. Thus the item remains a split, not a new Mathlib leaf.

## Unfinished work

None in this one-level split. Existing dependency nodes keep their own status; no Lean was written, no compiler/build was run, and all writes were inside this sandbox. Server dry-run and delivery results are supplied by deliver.py.
