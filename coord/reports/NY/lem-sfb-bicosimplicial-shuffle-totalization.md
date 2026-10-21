# Stage-1 report: lem-sfb-bicosimplicial-shuffle-totalization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bicosimplicial-shuffle-totalization.json`: statement; split with nine proof steps; no exact project Lean attachment and no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-simplex-lattice-shuffle-boundary.json`: new statement-only unsplit node; Mathlib searches returned no signed lattice-path boundary theorem. It has no proof or proof dependencies.
- `citations.json`: one verbatim statement excerpt for every step/node citation.

There is one new node and zero new Mathlib leaves. `check_small_cases.py` and `write_split.py` are sandbox-only working scripts, not project files.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, bicosimplicial objects, shuffles, Eilenberg–Zilber and Alexander–Whitney found no declaration stating this item. The finite-projective internal-Hom shuffle and Koszul sign references concern different operations. The module cup-product Alexander–Whitney files concern pairings, rather than this diagonal homotopy equivalence.

## Wanted literature

WANTED: C. Weibel, *An Introduction to Homological Algebra*, section 8.5, the Eilenberg–Zilber shuffle boundary calculation, for `lem-sfb-simplex-lattice-shuffle-boundary` and the parent. `literature/LIST.md` records the book as unavailable. I did not download or edit literature. The parent's proof is explicitly marked agent-written: the current blueprint states its geometric application but does not contain this universal free-simplex proof.

## Issues found

The assigned statement is correct as written, including the unnormalized complexes and the specified surjections. No statement was changed. In particular, the shuffle sign is the sign of the concatenated lists of increment positions, with the first list having length a; changing the coordinate assignment would change the formula.

The inherited `blueprint.from.node` is null. `python3 tools/blueprint_refs.py ancestor lem-sfb-bicosimplicial-shuffle-totalization` actually returns None. I preserved that inherited result, filled the child's precise application place and via chain, and recorded the current main-20261015 proof paragraph (3) rather than inventing an ancestor. Whole-blueprint searches for shuffle, simplex and projective-resolution lifts found no equivalent blueprint node. The historical unit JSON points to the older six-functors chapter, whereas this assigned item and its source live in six-functors-basics; I read both and followed the current source's formal open-direct-image comparison without altering the unit or chapter.

## Not duplicates

lem-sfb-simplex-lattice-shuffle-boundary vs lem-sfb-bicosimplicial-shuffle-totalization: the child is only a boundary identity for finite integral sums of weakly increasing pairs of vertex strings. It asserts neither homotopy equivalence nor arbitrary abelian coefficients, internal complexes, totalization or augmentation maps from a complex. The parent's resolution, evaluation, total-differential and strict augmentation arguments are proved in its own steps.

lem-sfb-simplex-lattice-shuffle-boundary vs lem-cbc-normalized-simplex-chain-diagonal: the existing node gives the Alexander–Whitney coalgebra diagonal on normalized free chains, discarding repetitions. The new node concerns the opposite-direction shuffle on unnormalized chains of two independent simplices and retains repetitions. Neither statement specializes to the other.

lem-sfb-simplex-lattice-shuffle-boundary vs lem-coef-bisimplicial-diagonal-equivalence: that node is a weak-equivalence statement about homotopically constant bisimplicial spaces. It supplies no signed integral shuffle boundary identity.

DAG searches also inspected the lattice-path hits for pattern-generator product cells, Cartesian twisted resolutions and nonfree-chain completions: their statements concern marked anodyne attachments, final functors or strict-chain completion counts, not an alternating-deletion identity. No existing node with the child's statement was found. No Stacks tag is assigned to the child: the local Stacks Eilenberg–Zilber statement in sites-cohomology.tex is a derived tensor comparison of simplicial modules, not this explicit shuffle formula or a homotopy inverse for arbitrary abelian coefficients, so I did not misattribute it.

## Mathlib search assessment

Every search in the new node was actually run with the prescribed msearch.py and recorded in searches.jsonl. Both semantic services were available; Loogle and source grep ran too. I tried two semantic formulations of the lattice-path identity. I read the product-simplex coordinate and face statements in AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean, the normalization homotopy equivalence in DoldKan/HomotopyEquivalence.lean, and ExtraDegeneracy.lean's stated hypothesis and conclusion. Product-simplex coordinate equivalences only identify coordinates and deletion; they do not assert the signed sum. Dold–Kan compares one simplicial object's normalized and unnormalized complexes, and extra degeneracy needs a specified contraction of a single augmented simplicial object. The alternating multilinear-map shuffle hits are not chain maps on pairs of simplices. None is an exact or one-line generalized match.

For the item I repeated semantic searches, Loogle and Homology grep with the full bicosimplicial/internal-complex question, retained the inherited search records, and read the returned normalization, extra-degeneracy and totalization candidates. ProjectiveResolution.homotopyEquiv and liftHomotopy really do give general comparison tools: I read Resolution.lean, but no new node was needed for them because the existing injective-resolution lift (dually) and augmented-resolution uniqueness nodes already supply the needed interfaces. The exploratory projective-resolution searches remain in searches.jsonl; they are not recorded as negative searches for the shuffle identity.

## Review by NY

I read the assigned node, its chapter and unit records, the current main-20261015 direct-images proof paragraph (3), the whole B–E checklist of delivery-errors.md (both copies), and the existing nodes cited below. I checked the simplex contraction against Stacks Tag 08Q3 (simplicial.tex, example-simplex-contractible), including its distinction between a first-vertex and last-vertex homotopy. The proof uses an explicitly written first-vertex chain contraction, so it does not assume a reversal of the source's simplicial homotopy. For resolution comparison I read derived.tex Tags 013P/0649 (morphisms-lift and morphisms-lift-projective) and 064A (morphisms-equal-up-to-homotopy-projective), the exact statements of the two cited existing nodes, and the Mathlib injective desc/desc_commutes definitions. The shuffle boundary child is sourced as agent-formulated with the missing Weibel reference honestly requested; the local blueprint and Stacks are not claimed to prove its formula.

Step 1 uses exactly the abelian-category definition. The pointwise kernel/quotient construction verifies it directly; the displayed generator formula proves the special additive Yoneda fact instead of citing the scheme-only Yoneda node. Lifting each generator proves projectivity, and the explicitly indexed coproduct surjects onto every diagram. I checked that I is small, so these auxiliary groups and coproducts exist in a fixed universe. This does not assume any infinite coproducts in the arbitrary target category C.

Step 2 uses the child's explicitly defined unnormalized string complexes and boundaries. The representations R_(n,n) and sum R_(a,b) evaluate to exactly its V and U tensor complexes, not to normalized chains. I checked both cross-term signs and the fact that boundary out of degree zero is zero. Step 3 proves the exactness rather than citing a generic acyclic-model assertion. Prepending the minimum vertex gives d h+h d=1-e epsilon in degree zero and 1 in positive degrees; on a tensor, H=h tensor 1+E tensor h gives 1-E tensor E. I checked that E kills positive degrees, the tensor signs cancel, and the degree-zero augmentations are surjective. Naturality of the contractions is neither true nor needed: only exactness is detected pointwise. Thus the hypotheses of projective resolution comparison hold in the functor category.

Step 4 cites the new child's boundary, augmentation and postcomposition claims, all present in its statement. It uses no homotopy-equivalence conclusion from the child. Evaluating the universal generator gives precisely (alpha_mu,alpha_nu), with the intended lengths, so the item will receive its own specified shuffle, not an unspecified comparison map.

Step 5 cites `lem-weil-pbc-injective-resolution-lift-exists` for the existence of a map of resolutions and `new-t4-augmented-resolution-lift-homotopy` for uniqueness up to homotopy. I opened both nodes. The former is stated for every abelian category and actual injective resolutions. Opposite projective resolutions meet this hypothesis because the abelian axioms dualize, epis become monos and enough projectives in Step 1 gives enough injectives in the opposite. Applying it in the order Q-op, P-op gives tau:P -> Q, not the reversed map. The latter node allows any exact nonnegative target, and here both targets are exact projective resolutions. Its required augmentation equalities follow from epsilon_P sigma=epsilon_Q and epsilon_Q tau=epsilon_P; d_1 followed by augmentation is zero. I declared its off-unit citation as a generic homotopy-uniqueness tool. This does not replace the unit's direct-image route.

Step 6 is a written finite-matrix argument: Nat(R_i,R_j) is the free group on arrows j -> i, so evaluating through the covariant X reverses the universal chain map. I checked this variance, matrix composition, and the reversal of degree +1 chain homotopies to degree -1 cochain homotopies. All matrices are finite sums of representables, and the argument uses only the finite biproduct and bilinear composition clauses of def-sp-abelian.

Step 7 uses def-sp-double-complex-total for finite first-quadrant total sums. The universal matrices commute with d_r since all their entries are X's structure maps. Degree-zero maps preserve the total cosimplicial index n=a+b, whereas a homotopy lowers it by one. I checked the actual internal cross terms (-1)^(n-1)d_r H+(-1)^n H d_r=0. Consequently the homotopies survive totalization, rather than merely proving that each row is a quasi-isomorphism. Step 8 uses precisely the localization from the homotopy category stated in def-weil-abstract-derived-category: an already invertible homotopy-category class stays invertible. It proves an isomorphism of derived objects and its naturality, rather than just cohomology isomorphisms.

Step 9 has no hidden lemma: the two degree-zero coface differences annihilate i, their commutation kills the diagonal coface difference, and the only degree-zero shuffle is the empty partition with sign 1. Thus the asserted square commutes strictly as chain maps. Zero objects, constant diagrams and one constant direction require no reduced/normalized or nondegeneracy assumption. I tested the child's formula exhaustively on 1,969 basis pairs with p,q <= 2 and a+b <= 4, including repeated vertices, p=q=0, and each zero-dimensional factor, using the sandbox-only check_small_cases.py; every signed boundary identity passed. I also checked the zero-degree vertex/augmentation equation and the zero complex directly.

For B1–B9 I checked self-contained objects, definitions or explicit inline meanings, honest sources, unsplit-child emptiness, actual search logs and blueprint origins. For C1/C4 I compared each step's uses with the exact cited statements and generated all verbatim quotes in citations.json. For C6 there is no upward edge: the child has only the module-chain-complex statement dependency, and the existing generic lift/homotopy nodes do not depend on the item. For D1/D2 the substantive resolution construction and totalization proof remain in the item. For D4 the resolutions are verified before comparison is applied. For E1–E5 I checked the hypotheses and the coordinate, variance and total-sign calculations above. Every step is under 2,000 characters, so no long step hides an additional comparison lemma. No statement dispute or source error was found.

## Unfinished work

No part of this one-level split is omitted. The child is intentionally statement-only and joins the stage-1 queue; it is not claimed proved or in Mathlib. Formal Lean writing and all compilation remain outside this task.

## Dry-run repair

The first dry run found one schema issue: the completely explicit combinatorial child had no definition-node citation. I opened def-weil-pbc-module-chain-complex-homology, verified that it defines precisely the integer-indexed module chain complexes and chain maps used here (including extension by zero), and added it as the child's statement dependency with R=Z. I refreshed the parent's verbatim child quotations. The child still has no proof or proof dependencies; the mathematical statement and its searches are unchanged.
