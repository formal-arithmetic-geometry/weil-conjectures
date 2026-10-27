# Q54 stage-1 delivery: lem-sfb-smooth-affine-normal-quotient-lifts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-affine-normal-quotient-lifts.json: split the item into eleven proof steps; no new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement excerpt for every node used by every step (31 entries), checked against the current read clone.
- report.md: this report. The sandbox also contains the extracted Milne text, the preparation script and the actual search log; these are working material, not node deliveries.

## Attachments

None. I searched the entire live lean/WeilConjectures tree for the exact blueprint tag and for quotient/group-scheme and affine-extension terminology, then read the GroupScheme matches. The available closed-subgroup, kernel and identity-component constructions do not assert existence of this quotient or the inverse-image conclusion. I wrote no Lean and ran no compiler.

## WANTED

None. The cited Milne book and Stacks sources are available locally.

## Corrections and route

The mathematical statement is unchanged. I repaired doubled TeX backslashes in the imported statement, including the displayed arrows and fibre product. There is no statement dispute. The source of the item is Milne's Algebraic Groups (2017), Theorem 5.14 and its proof after Theorem 5.28, Propositions 5.24--5.25, Corollary 5.26, Proposition 1.62, Theorem 5.55, Proposition 5.59 and Proposition 8.1(a). I extracted the PDF and read those places, including the nonaffine quotient argument on printed p.105. In particular, the book does not require the ambient group to be affine or commutative.

I read GOAL.md, the three-level restrictions in SETUP.md, the chapter/unit records, and the latest blueprint chapter and sk-thm-sf-ctf-stability unit. This is a foundational group-theoretic branch of the existing finiteness route, not a replacement for a unit step. blueprint_refs.py ancestor reports None for this item; its existing ancestry and precise Milne place are retained. Searches across the whole blueprint for normal subgroup, quotient group, homogeneous quotient and affine normal produced no equivalent imported node. Whole-DAG searches found the existing homogeneous quotient and affine connected-extension results and the scheme/descent tools used here. No node was created.

Two unsplit-proof tools of other units are explicitly declared in split_report.tool_uses: lem-weil-pbc-fpqc-descend-affine (affineness descends from the torsor trivialization) and lem-sbc-smooth-flat-surjective-source-descent (the smooth source makes Q smooth). They are general foundational scheme tools, not alternate finiteness routes; no statement in the item's unit replaces these properties. The smooth base-descent and other tools are already leaves or closed where applicable.

The item already carried its creator's Mathlib searches, which I retained and read. I additionally ran the prescribed msearch command for LeanFinder, LeanSearch, Loogle and Mathlib grep under this item. The semantic hits are abstract/topological group quotients and affine spaces, not quotient group schemes. Loogle for GrpObj with IsSmooth and grep in AlgebraicGeometry/Group had no matches. The two semantic phrasings differ and the original item's additional phrasings are retained. I recorded only actual logged searches; none was unavailable in this run.

## Unfinished work

None in the authorized one-level stage-1 split. Existing dependencies retain their own stage status. The server review_split check has passed. Final delivery preflight is recorded below after it exits.

## Not duplicates

No new nodes, hence no new/existing duplicate pairs. In particular I did not introduce another normal quotient node or an affine-extension node: I used lem-sfb-algebraic-group-homogeneous-quotient and proved the group law, and I used the already present affine connected-group-extension result only after proving its affineness hypotheses.

## Review by Q54

I checked sections B--E of delivery-errors.md against the proof and the cited statements, not just the dependency names. Milne supplies the quotient, torsor, normal correspondence and extension route; Stacks descent.tex supplies the exact universal effective epimorphism statement (023Q), affineness descent (02L5), and smooth base descent (02VL). I read the corresponding Stacks statements and proofs and checked the tag/label table. During this review I corrected the proof-source tags for flat base change to 01U9 and for the definition of an fppf covering to 021M. The existing definition node also mentions the fppf section tag 021L, but its written covering condition is correct and is the condition used.

Step 1 uses the full statement of lem-sfb-algebraic-group-homogeneous-quotient: it applies to separated finite-type groups with any closed subgroup, and supplies the test-scheme coset criterion as well as flatness, surjectivity and finite presentation. The natural bijection giving the kernel-pair isomorphism uses exactly the bijection of morphisms and natural transformations in lem-galois-yoneda-fully-faithful. The proof that q is an fpqc cover is written using the affine-open covering definition in def-weil-pbc-fpqc-covering. No quotient group structure is taken from the homogeneous-space statement.

Step 2 uses lem-galois-fpqc-covering-base-change for q times an arbitrary parameter scheme, and lem-weil-pbc-fpqc-representable-descent for descent of compatible morphisms and its uniqueness. The latter's statement supplies existence and uniqueness, not merely full faithfulness of Yoneda. The kernel pair and both projections are explicitly identified. This proves the parameterwise descent and equality test used in steps 3--4, so no additional implicit descent theorem is being cited there.

Steps 3--4 use the written definitions of normal subgroup and group scheme. I checked the noncommutative identity (g1 n1)(g2 n2) = g1 g2 (g2^-1 n1 g2) n2 and the inverse identity (g n)^-1 = g^-1 (g n^-1 g^-1). The two descents and the intervening invariance check are described. Associativity, both units and both inverses are checked after the previously proved injective precomposition maps. These are explicit routine applications of the earlier descent step, not a theorem about normal group-scheme quotients hidden in a new clause node. Step 5 uses the fibre-product definition and Yoneda to identify the actual scheme-theoretic kernel, on all test schemes rather than only k-points.

Step 6 reads the kernel pair as the base change of q along q, with projection to the first G factor, and uses affine and smooth base-change statements for the projection G times N to G. The source affine-morphism definition and affine permanence node state exactly the affineness assertion needed, and lem-pc-proper-base-change has a separate smooth base-change clause (2), despite its title. Affine descent and smooth base descent then apply to the flat, quasi-compact surjection q already obtained. In step 7 the source-descent node assumes flat, surjective and locally finitely presented q, all supplied in step 1; its composite is G to Spec k, smooth by hypothesis. Connectedness of Q is proved directly from surjectivity and the connected-space definition; I also made its nonemptiness explicit using the unit point.

Step 8 separately cites flat base change, surjective base change and qcqs/finite-presentation base change, then reads the covering clause from def-pc-fppf-site. It does not assume T is finite type or quasi-compact. Step 9 uses closed-immersion base change, the normal-subgroup definition and fibre-product pasting: P is the scheme-theoretic inverse image, and its kernel after pullback to the unit of S is exactly the kernel from step 5. The maps and conjugation identity are stated on all affine test schemes, where the defining normality condition applies.

Step 10 uses the affine permanence node both for base change and for affine source over an affine target. It proves finite type before using a group-extension lemma: a closed immersion is proper by lem-weil-pbc-proper-fp-permanence(c), proper implies finite type by the properness definition, and lem-sfb-finite-type-composition-base-change(1) composes with G's structure map. Step 11 uses smooth base change and the existing smooth-composition leaf, then applies lem-sfb-connected-group-extension only to P and S, both now affine finite type. The original ambient G and the quotient Q are never fed to that affine-only lemma. Its kernel is N by step 9, and flatness/surjectivity and connectedness hypotheses are all present. I read each of these node statements and checked every citations.json excerpt literally against it.

For small cases I checked N = 1 (q is the identity up to the constructed isomorphism), N = G when G is affine (Q is the trivial group), S = 1 (P = N), S = Q when Q is affine (the argument proves G affine), and an abelian-variety ambient group with trivial N (nothing incorrectly forces Q affine). The trivial smooth connected group is allowed. Nonreduced test schemes are retained throughout; kernel and normality checks do not replace scheme points with geometric points. A characteristic-p non-smooth kernel such as mu_p is outside the item's hypotheses, so the proof does not infer a Frobenius quotient map smooth without smooth kernel. I checked empty T for the covering clause as well.

All steps are shorter than 2000 characters. There are no new elementary, duplicate, clause-restating or Mathlib-matched nodes, no cited proof used in place of its statement, and no source called standard without the corresponding argument or cited node. The report signs the resulting split for the maintainer's independent review.
