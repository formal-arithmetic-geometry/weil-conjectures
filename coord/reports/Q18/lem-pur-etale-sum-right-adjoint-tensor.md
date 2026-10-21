# Stage-1 report: lem-pur-etale-sum-right-adjoint-tensor

Group Q18, 2026-10-21. Direct delivery with self-review as authorized in the brief.

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-etale-sum-right-adjoint-tensor.json`: existing statement node, split into nine steps; not a Mathlib leaf. The statement, statement dependencies and inherited blueprint fields are unchanged. Added the split report and searched the blueprint for alternate versions (none states this map equality).
- `citations.json`: 27 exact statement excerpts, one for each node cited by each step.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. `searches.jsonl` is the unmodified output log of the required msearch commands. The two sandbox Python scripts only assemble and check the JSON; neither is a project delivery file.

## Attachments

None. Searched the project source for the blueprint tag, sum extension/evaluation, and etale tensor/counit notions. Read `WeilConjectures/SixFunctors/Etale/LowerShriek/EtaleMap.lean` (definition and ordinary sheaf adjunction), `EtaleMapProjection.lean` (sheaf projection and naturality), and `Derived/SmoothDuality/Charts.lean` (EtaleSmoothDuality is an assumed proposition). None gives this complete normalized derived map equality, refinement independence and open restriction. The sheaf projection alone cannot attach the item. No Lean was written and no compiler was run.

## WANTED

None. The needed local Stacks sources and the current blueprint were available.

## Defects and changes

The item was an unsplit, precise refinement of the blueprint's assertion that the etale tensor map is the identity. Its statement is correctly typed and no statement dispute was found. The blueprint's word “immediate” does not supply the required normalization calculation, so the split writes it out. The existing proper-support/projection compatibility node supplies the crucial specified-map identity; an abstract projection formula would not suffice. The proof never treats the sheafified sum as an objectwise presheaf sum, and never treats geometric stalk cohomology as faithful on derived morphisms.

The item descends from the current composition-coherence proof Step 1 through diagonal-section-pasting and finite-etale-dualizing-normalization. This argument realizes that route's etale normalization/co-projection calculation; it introduces no trace/purity alternative. The chapter and unit records were read and left unchanged. Generic off-unit sheaf and homological tools are declared in `split_report.tool_uses` for the maintainer; no top-level tool approval was written.

## Mathlib and duplicate checks

Read the inherited search results and retained all their queries and results. Additionally ran msearch with two LeanFinder phrasings, Loogle on `CategoryTheory.Adjunction, CategoryTheory.conjugateEquiv`, LeanSearch on the etale sum/tensor normalization, and grep on `sumExtension|etale.*(shriek|dualizing)|shriek.*tensor`. The first LeanFinder returned etale commutative-algebra presentation results; the second returned ordinary sheaf/constant-sheaf counits. Loogle supplies general conjugacy already represented by the existing Mathlib leaf `def-weil-pbc-adjunction-conjugate`; its source Mates.lean was read at the definition and counit identities. LeanSearch supplies Kan-extension counits and a coalgebra tensor counit. None is this derived geometric assertion or its one-line specialization. Grep had zero hits. All new search entries reflect actual commands; no service was recorded as absent when unavailable.

Searched the whole DAG by the sum/evaluation and projection/counit concepts, then read the candidate statements, including `lem-amb-tensor-projection-adjunct`, `lem-asd-adjunction-projection-map-mate`, `lem-pur-composite-tensor-transpose`, `lem-asd-tensor-mate-etale-precomp`, and the support-map and chain-model nodes used below. The first concerns inverse image adjoint to direct image, not sum extension adjoint to restriction; the transport lemma assumes a projection defined as a mate, and does not identify our given geometric projection. Thus neither was substituted for the required generator calculation. `tools/blueprint_refs.py search` on “projection counit”, “etale normalization”, “sum extension”, “right adjoint tensor”, and “sum-evaluation” found no alternate blueprint statement of the full item. Ancestor was checked with the ancestor command. No new node was needed: the new content consists of short generator calculations, naturality, and transposition between existing results.

## Not duplicates

No new nodes; hence there are no new/existing same-tag pairs to distinguish.

## Review by Q18

I read the current `main-20261015` proof of `lem-pur-co-smooth-etale-locality`, Step 1, and Stacks `more-etale.tex`, Tag **0GKF**, label **lemma-f-shriek-projection**, including the pure-tensor construction and its stalk square. For open restriction I read `etale-cohomology.tex`, Tag **03S6**, label **lemma-shriek-base-change** and its adjunction argument. I also read `sites-modules.tex`, Tag **0E8I**, label **lemma-j-shriek-and-tensor**: it supplies an abstract Yoneda projection isomorphism, which is not enough to fix the generator normalization. No SGA source is used. There is no new node needing a separate source review.

Step 1 uses the statements of the existing conjugate and mate definition nodes: the former explicitly gives the isomorphism/bijection assertions, the latter the counit transpose formula. I checked directions: the conjugated arrow is d inverse, from S to F, so its right arrow is G to e*. I wrote the inverse-transpose calculation establishing equation (1), rather than assuming arbitrary right-adjoint isomorphisms preserve the chosen counits.

Step 2 uses the actual generator formula of `lem-pur-etale-sheaf-projection-map`, the lift-indexed definition, the universal property of module sheafification, and the exact ordinary sum/restriction adjunction from `lem-weil-pbc-etale-restriction-injectives`. The etale inverse-image restriction node explicitly identifies restriction on test objects; its underlying abelian statement also respects the constant-ring action. On each generator both paths yield b times h. This is an elementary calculation, not a separately asserted compatibility theorem. It takes place before sheafification; factorization uniquely gives the sheaf map identity.

Step 3 cites each analytic ingredient it actually needs: flat-term K-flat resolutions, pullback preservation of flat-term K-flat complexes, sum-extension preservation of them, the signed totalization generator formula, the termwise unbounded adjunction, termwise adjunction on complexes and homotopy categories, tensor descent, and localization faithfulness. Their statements were opened in full. In particular the totalization node explicitly covers arbitrary unbounded complexes and fixes differential signs; the pullback and sum-extension nodes explicitly preserve K-flatness. Only the second tensor factor varies here, so no two different sites are silently identified in a bifunctor localization. The first factor is the coefficient unit, flat and K-flat because tensor with it is identity. Evaluation and all displayed maps preserve degree, so equality of the complex maps follows degree by degree and descends. No boundedness or constructibility condition on K is used.

Step 4 quotes clause (2) of `lem-pur-etale-support-map-compatibility` verbatim, with its specified proper/open projection. It is applied at M=W and this node allows every unbounded M,K, including W=G(A). Tensor symmetry is supplied by `lem-kun-tensor-sym`. I checked the inverse directions by solving d P = p(d tensor 1), which gives exactly formula (4), after naturality of d at symmetry.

Step 5 uses the already proved equations (1),(3),(4) and naturality of p. I checked each domain: S(W tensor TK) maps by p inverse to SW tensor K; after S(rho at A) the latter is S(TA) tensor K. Formula (3) then cancels p at (TA,K). This is a short algebraic substitution, so it creates no lemma node. Symmetry converts the left unit action to the displayed right unit action with eta; the signed symmetry is not replaced by an unsigned interchange.

Step 6 applies the mate node's inverse-transpose formula and injectivity of the Hom bijection. It is the requested map equality, not just an isomorphism claim or equality after cohomology. Naturality was retained throughout.

Step 7 takes compactification independence from the quasi-finite proper-support comparison and refinement compatibility of the specified projection from the last sentence of support-map compatibility. These statements explicitly cover compactifications whose proper map is not finite. Conjugacy defines the right comparison with the correct inverse direction. I checked rho' r = rho and consequently eta' r at A = eta, and then the stated tau comparison by transposition. The refinement cocycle follows from composition of conjugates and the canonical left comparisons already given; no new choice is made.

Step 8 explicitly uses the fibre-product universal property for the open lift correspondence, the module sum base-change theorem, clause (1) of support-map compatibility, the sum-composition clause of the quasi-finite comparison, exact sum/restriction adjunctions, and the changing-adjunction mate-pasting rule. The citations file quotes precisely those clauses, not an unrelated identity from the same node. The right restriction comparison is displayed. It is the conjugate of the comparison between F_e h! and g! F_e', since eh=ge'; under d this is the nested-summand comparison stated in the quasi-finite node. This verifies canonical normalization, not just existence of an isomorphism of right functors. For the pulled-back open square, X' and U' are open subschemes of the Noetherian schemes in the hypotheses, hence Noetherian, and the separated etale finite-type hypotheses and compactification base change remain those of the support-map node. Step 9 then pulls back the proven equality and cancels the invertible rho for e'; its unit and projection identifications are the ones just checked, so it introduces no uncited general base-change theorem for exceptional functors.

I checked B–E against these files. B: no new or proof-bearing unsplit nodes; preserved all imported metadata and single-escaped TeX. C: every non-elementary input is cited, every cited statement was read, and every excerpt is a literal substring. D: no relabelled clause nodes and no proof has been moved wholesale elsewhere. E: hypotheses include a finite commutative ring (not necessarily a field or of invertible exponent), arbitrary unbounded K, separated etale finite type, Noetherian bases, and a chosen compactification. Tested the identity map (d and rho give the identity normalization), the empty source (unique maps between zero functors), a two-sheet etale disjoint union (evaluation is the sum of the two components), an open immersion not surjective (zero extension outside the open), and K shifted by an arbitrary integer (the coefficient-unit action has degree zero). The formulas pass these cases. Each step is below 2000 characters; the longest is the explicit chain-model descent, whose non-elementary ingredients are the statements cited there. Corrections during review: added the explicit restriction/unit node in Step 2, and replaced generic citation excerpts in Steps 7–8 by the actual refinement/exchange/composition clauses used. No statement weakening or source correction was necessary.

## Unfinished work

None in this one-level split. The reused unsplit or sorried dependency nodes remain their own items. The required server dry run and push follow this report; delivery output is authoritative for completion.
