# Stage-1 report: lem-sfb-semisimple-centralizer-maximal-tori

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-centralizer-maximal-tori.json`: statement, split; retained the statement and its statement dependencies, added a five-step proof using existing nodes. Mathlib searches found no match.
- No new nodes; no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation per step/node citation.
- `searches.jsonl`: actual Q125 search log, produced by msearch.py. The item's inherited Q17 searches are retained alongside the new Q125 searches; no inherited log entries were invented.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, semisimple-centralizer phrases, and maximal-torus names. There is no project declaration stating the item. Abstract Cartan subalgebra results and root-system matrix constructions are different objects.

## WANTED

None. The item source and all structural inputs needed here are available in the repository.

## What was wrong or incomplete

The imported auxiliary statement is accurate in its faithful-matrix formulation and needs no correction. Its proof was empty. The source's proof of Milne 17.90 implicitly treats a nonzero X when saying that its centralizer cannot be unipotent. The item explicitly includes X=0, so the split does not use that shortcut, nor any assertion that a nontrivial torus exists. The Cartan product may have either factor trivial.

Milne's unipotent-quotient inference needs compatibility of semisimplicity with differentials of algebraic group representations; it does not follow merely from a definition of unipotence. The split cites the existing additive Jordan theorem and the existing unitriangular embedding theorem, and spells out the tangent matrix calculation. It uses algebraic group representations throughout, not arbitrary representations of an abstract Lie algebra.

There is no separate imported blueprint node for this item. `blueprint_refs.py ancestor` returns None. I retained its inherited null ancestor, long precise `from.place`, and `via` chain. I read the current latest chapter and unit, and the latest direct-image proof (3), which refers to proper direct image and open-immersion direct image. The Cartan argument is an inherited structural prerequisite below that route, not a replacement of a unit step. Blueprint searches for Cartan, semisimple, and semisimple centralizer yielded no equivalent imported statement. The inherited blueprint location is preserved.

## Not duplicates

No new nodes were created. Existing results already supply every non-elementary fact: smooth tangent stabilizers, geometric maximality of tori, the neutral Cartan product, geometric unipotence as a unitriangular embedding, and algebraic additive Jordan compatibility. The split does not create an extra node for the elementary strictly upper triangular/diagonalizable matrix argument or for descent of membership in a vector subspace. There are no new/existing node pairs to distinguish.

## Review by Q125

I read Milne, Algebraic Groups (iAG2017), Proposition 17.90 and its proof on printed p.381, with Proposition 17.76 and Example 17.75 on p.377, Proposition 17.28 on p.360, Theorem 16.47 and Corollary 16.48 on p.341, Theorem 17.82 on p.379, Proposition 1.34 on pp.16–17, and the unitriangular realization in Theorem 14.5 on pp.281–282. These are the precise source locations behind the existing nodes used in the split. No new node requires an additional source. I read the statement of each cited node, not just its title or proof, and checked the following applications.

Step 1 uses `lem-sfb-semisimple-tangent-stabilizer` for both smooth closed representability and the exact Lie centralizer formula. It has exactly the faithful closed representation and diagonalizability hypotheses in the item; it includes X=0. Its formula puts X in Lie(H) by [X,X]=0. `lem-sfb-finite-type-group-identity-subgroup` supplies the open and closed connected subgroup K without a perfectness hypothesis. Smoothness of K is the open-restriction statement of `lem-weil-pbc-smooth-restrict-open-subschemes`. The factorization of the one-point dual-number spectrum into K uses exactly the image-in-an-open hypothesis of `lem-weil-pbc-morphism-factors-through-open-subscheme`. `lem-pc-proper-base-change` is used only for its explicitly stated smoothness clause (2), never for cohomological base change. The connectedness theorem `lem-sbc-connected-rational-point-geometrically-connected` applies because K is connected and has its identity section. `lem-sfb-maximal-torus-field-extension` applies to this smooth connected affine finite-type K with its closed torus T; no reductivity is needed. `lem-sfb-affine-group-lie-tangent-calculus` gives the natural tangent scalar-extension isomorphism. The stabilizer functor itself says that T_F fixes X_F. I deliberately avoid assuming that identity-component formation over an arbitrary field commutes with extension; it is unnecessary here.

Step 2 applies `lem-sfb-neutral-torus-centralizer-cartan-structure` only over F, the algebraic closure, to K_F and the maximal T_F obtained in step 1. Its statement gives smooth connected C and an actual group-scheme product U times T_F. Its separate assertion about semisimple rational group points is NOT used for the tangent vector X_F. Instead `lem-sfb-affine-group-dual-number-calculus` supplies the scalar-extended infinitesimal-point bijections, their conjugation formula and naturality. I checked the whole-torus quantifiers: for every algebra R and every T_F(R)-point the invariant tangent vector commutes after passage to R[delta], and delta may be specialized to the image of epsilon in every dual-number algebra. Thus this really is membership in the scheme centralizer, not just commutation with F-points or with Lie(T). The centralizer node gives C as its open identity component; the open-factorization node then puts X_F in Lie(C). No normalizer representability hypothesis is smuggled in by citing a theorem that also discusses normalizers.

Step 3 uses the unipotence formulation of the Cartan node exactly as written: U is smooth and has a faithful representation whose geometric matrices are unipotent. These are all the hypotheses of `lem-sfb-geometric-unipotence-unitriangular-embedding`, which gives a closed immersion into upper unitriangular matrices over F. The embedding i_F restricted to C remains closed and faithful; its tangent matrix at X_F is diagonalizable. The arbitrary-field final clause of `lem-sfb-algebraic-lie-additive-jordan` therefore applies to the algebraic representation j composed with the product projection p, so its differential is diagonalizable. The Lie-tangent calculus node supplies the explicit I+epsilon A formula, differential functoriality and tangent injectivity for a closed immersion. The equations defining the unitriangular subgroup force A to have all diagonal and lower entries zero. Its mth power is zero, and a diagonalizing basis then makes A zero, since a field has no nonzero nilpotent scalars. Injectivity of dj gives dp(X_F)=0. Finally the group-scheme product from step 2 identifies tangent vectors with pairs directly by taking kernels on dual-number points; the first projection has kernel Lie(T_F). These are elementary calculations from the cited statements, not a new independent structural lemma. The step is under 2000 characters.

Step 4 cites only the tangent scalar-extension assertion of `lem-sfb-affine-group-lie-tangent-calculus`. I wrote out the basis argument proving descent of subspace membership, so no descent theorem or unjustified identification is hidden. Injectivity of the field embedding suffices even for an imperfect base. It is marked elementary because the only additional work is this coordinate calculation.

Step 5 uses the conjugation formula and subgroup compatibility in `lem-sfb-affine-group-dual-number-calculus` for every test algebra. An overtorus S is commutative as a group functor; its conjugation action fixes Lie(S) and hence X. The defining stabilizer functor gives S into H. The image of a connected space containing the identity lies in its identity component, and `lem-weil-pbc-morphism-factors-through-open-subscheme` turns this into an actual scheme map into K. The closed-immersion claim is checked on the quotient coordinate-algebra maps, not inferred merely from a pointwise inclusion. Maximality of T inside K now proves S=T. This proves the assertion for every containing k-torus directly, so an additional ambient maximal-torus existence theorem is unnecessary.

I tested X=0, central X, G a torus, G unipotent, the trivial group, a rank-zero maximal torus, and groups over imperfect fields of positive characteristic. For X=0 the calculation yields Lie(T)=0 in a unipotent group without a contradiction; for a torus the Cartan unipotent factor is trivial. With a rank-zero T, the same strictly upper triangular argument forces X=0, and the proof still applies. No division by a characteristic or nonzero eigenvalue is used. I kept the item's faithful-matrix definition and did not substitute abstract-Lie semisimplicity. There is no statement dispute.

For delivery-errors B–E, I checked that all objects and hypotheses stay introduced by the unchanged statement and its definition dependencies; that every non-elementary proof input is an existing cited statement; that no step uses facts found only inside another node's proof; and that none of these nodes depends transitively on this item. The finite product tangent kernel and the matrix calculation remain explicit proof steps rather than duplicate nodes. Every step is shorter than 2000 characters. All quotations in citations.json were checked as literal substrings of the corresponding live node statements. Q125's actual searches cover LeanSearch, LeanFinder (two distinct mathematical phrasings), Loogle and source grep, with no exact match. The five search outputs were read. The inherited search records were preserved. No Lean file or repository file was written and no compiler, Lake or build tool was run.

Two generic tools cross unit boundaries and are declared in split_report.tool_uses: the smoothness-under-base-change clause of `lem-pc-proper-base-change`, and connectedness after a field extension from an identity section, `lem-sbc-connected-rational-point-geometrically-connected`. They only justify scalar extension of K; they do not change the unit's route. All structural algebraic-group inputs are in the item's unit.

## What could not be finished

None mathematically. Required server preflight and delivery results are recorded below after they complete.

## Validation

The required `deliver.py Q125 lem-sfb-semisimple-centralizer-maximal-tori --no-push` exited 0 and printed `OK (not pushed)` at 545e6ea6d50. Server preflight passed. There were no failure diagnostics to repair. This report records that completed check; the final report is then checked again before pushing.
