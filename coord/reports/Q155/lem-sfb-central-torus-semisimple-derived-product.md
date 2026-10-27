# Worker report

## Files written

All node paths are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-central-torus-semisimple-derived-product.json`: item, split; statement unchanged; seven steps.
- `lem-sfb-affine-group-homomorphism-image.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-smooth-connected-derived-subgroup.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-semisimple-group-perfect.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-semisimple-isogeny-source.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-central-torus-faithful-weight-blocks.json`: statement, unsplit, no Mathlib match.
- `lem-sfb-split-torus-subgroups-diagonalizable.json`: statement, unsplit, no Mathlib match.

`citations.json` contains verbatim statement quotations for every citation in every proof step. New nodes have statements only, empty proofs and proof dependencies. No Lean, unit, chapter, repository, or launcher source was changed.

## Attachments

None. Searched `lean/WeilConjectures/` for the item tag, central tori, semisimple groups, derived subgroups, and faithful representations. `GeneralLinear/ClosedSubgroup.lean` contains a derived-ideal construction, but not the smoothness, connectedness, rational-point generation, or semisimple-product assertion. The semisimple representation and Lie algebra declarations do not assert semisimplicity of affine group schemes.

## WANTED

None: every mathematical source needed here is in Milne, *Algebraic Groups*, `literature/milne-algebraic-groups_iAG2017.pdf`.

## Corrections and scope

The original statement is true and was preserved. Its scheme-theoretic intersection must not be replaced by its reduced subgroup. Milne 12.46(a) proves finiteness using rational points; I refined that proof using the actual block determinant morphisms and a finite coordinate algebra, so no rational-point-to-dimension lemma is hidden. Semisimplicity of the derived group is obtained using Milne 19.14, exactly the isogeny argument in the proof of 21.60(b) implies (c), without silently assuming that G is already reductive.

The original node had no proof. I added the subgroup definition to its statement dependencies. No source statement was disputed. The current blueprint was read in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, including the section and direct-images proof. This is a subordinate Milne/Haboush central-cover input in the inherited alteration/moduli route. The ancestry tool reports `None`; I preserved that null ancestor and extended its inherited via list for new nodes rather than inventing a blueprint id. This node does not state the unit, so no unit realization was edited.

## Search record

For each new node, `search_results.json` records actual output from two LeanFinder phrasings, Loogle, grep and LeanSearch. The same queries and their outputs are in each node's `mathlib_searches`, with no service failure misreported as absence. The required searches were run through msearch.py with Q155 and this item, recorded in this sandbox's searches.jsonl. Additional searches of the item and linearity were also made, and the original item's recorded searches were retained. The initial exploratory calls using candidate node ids as the search item's argument were repeated under this item's argument to put the required records in the delivery's log.

I read the search hits: the flatness equivalence in `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:170` assumes both flatness and surjectivity and supplies neither the group homomorphism image theorem nor automatic flatness from rational-point surjectivity. `MonoidAlgebra.instHopfAlgebra` in `Mathlib/RingTheory/HopfAlgebra/MonoidAlgebra.lean` constructs a Hopf structure on a group algebra but does not classify quotient Hopf algebras of tori. The other hits are abstract commutator subgroups, Lie algebras, finite abstract-group representations, or semisimple linear maps. None is a one-line specialization giving these group-scheme statements.

DAG searches covered the whole tree by source numbers 5.39, 5.47, 6.19, 6.20, 21.50, 19.14, 4.9, 12.12 and 12.9 and the notions faithful representation, derived subgroup, diagonalizable, isogeny and semisimple group. Blueprint searches included derived subgroup, semisimple, diagonalizable, faithful representation, homomorphism, isogeny, torus, regular representation and weight. Existing abelian-variety and characteristic-zero Lie-algebra assertions were read and rejected for the precise hypothesis differences below.

## Not duplicates

lem-sfb-affine-group-homomorphism-image vs lem-sc-image-subgroup: the existing image theorem assumes a proper source; it does not give faithfully flat image factorization, the quotient projection or the smooth-target rational-point criterion needed for these affine sources.
lem-sfb-affine-group-homomorphism-image vs sk-p-geometry: the blueprint assertion uses the characteristic-zero matrix-group convention and gives closed images, not faithful flatness or the quotient and rational-point criteria in arbitrary characteristic.
lem-sfb-affine-group-homomorphism-image vs lem-sfb-abelian-hom-image-dimension: the latter concerns abelian varieties and their dimensions, not general affine group schemes.
lem-sfb-smooth-connected-derived-subgroup vs sk-i-restriction: the latter concerns a represented degree datum and semisimple modules, not general smooth affine derived subgroups or equality with abstract rational-point commutators.
lem-sfb-semisimple-group-perfect vs lem-ag-central-radical-quotient: the latter concerns a characteristic-zero Lie algebra, not a semisimple affine group scheme in arbitrary characteristic.
lem-sfb-semisimple-isogeny-source vs lem-sfb-semisimple-multiplicative-universal-cover: the existing node constructs a special universal cover, and assumes its target semisimple; it does not state preservation of semisimplicity under an arbitrary finite-kernel faithfully flat homomorphism.
lem-sfb-central-torus-faithful-weight-blocks vs lem-sfb-gm-representation-weight-basis: the existing lemma decomposes an already given representation of a single G_m. It supplies neither a faithful finite-dimensional realization of an arbitrary affine group scheme, nor stable blocks for a central torus of arbitrary rank, nor their closed-immersion character tuple.
lem-sfb-split-torus-subgroups-diagonalizable vs lem-sfb-multiplicative-type-largest-subtorus: the latter defines multiplicative type as embeddability in a torus after closure; it does not identify its Hopf algebra with F[M] or give the finite character-group classification required by this item's definition.
lem-sfb-split-torus-subgroups-diagonalizable vs lem-sfb-split-torus-hom-matrices: the existing node classifies maps between tori, not arbitrary possibly nonreduced closed subgroups.
lem-sfb-smooth-connected-derived-subgroup vs lem-sfb-central-torus-semisimple-derived-product: the new node is a general foundational derived-subgroup fact without a central torus or semisimple quotient; the item's determinant, finite-kernel, multiplication and semisimplicity arguments remain in the item.
lem-sfb-semisimple-group-perfect vs lem-sfb-central-torus-semisimple-derived-product: perfectness of an arbitrary semisimple group is a separate input used on the quotient, not a clause asserting this item's almost product.
lem-sfb-central-torus-faithful-weight-blocks vs lem-sfb-central-torus-semisimple-derived-product: faithful representations and torus weights hold without any assumption on the quotient and do not assert intersection finiteness or multiplication surjectivity.

## Review by Q155

I read Milne 12.46(a),(b), pp.245--246, and its example 12.47, not just its statement. I also read the derivation in 21.60(b) implies (c), p.442; it uses perfectness and an isogeny to the semisimple quotient. This determined the proof route. The source for each new input was opened: 5.25, 5.39, 5.42 and 5.47 for images and quotients; 6.18--6.20 for derived subgroups; Corollary 21.50 for perfectness; Lemma 19.14 for isogeny sources; Theorem 4.9, Corollary 4.10, Theorem 12.12 and the weight-block argument of 12.46 for faithful weight blocks; Theorems 12.8--12.9 and Section 12.14 for diagonalizable subgroups. The item cites no SGA source. Theorems here are Milne results, not assertions for which an unrelated Stacks tag was substituted.

Step 1 uses precisely the smooth-connected-derived node's smoothness and rational-point equality, the perfectness node's equality for Q, and the image node's quotient projection and smooth-target criterion. Both G and Q are smooth connected affine finite-type groups over the given algebraically closed field, so every premise is present. The only group calculation is lifting each factor of a product of commutators under a surjective abstract homomorphism. This is written explicitly.

Step 2 uses the weight-block node's faithful representation and stable finite-dimensional blocks and the derived-subgroup node's vanishing for homomorphisms to commutative groups. That last clause is a morphism-level assertion, so determinants vanish on infinitesimal points as well. I checked the quoted statements themselves, rather than taking more from their proofs.

Step 3 has no new non-elementary input: it takes the closed immersion already supplied in step 2 and the equations already proved there, and writes the quotient of a Laurent polynomial ring and a finite spanning set. The quotient algebra remains finite-dimensional in every characteristic. It is marked elementary for this explicit coordinate calculation, not for Milne's whole finiteness theorem.

Step 4 uses exactly the new isogeny-source assertion. D's smoothness and connectedness were obtained in step 1, faithful flatness in step 1, and scheme-theoretic kernel finiteness in step 3. The kernel identification with the fibre product is the definition of intersection and of the quotient's kernel. There is no assumption of reductivity added to the item.

Step 5 uses the image node's rational-point criterion with smooth target G. The preceding multiplication identity uses the assumed centrality, and the displayed decomposition g=(gd^{-1})d uses the surjectivity of D(F) onto Q(F) established in step 1. The kernel of q is R, because q is the stated fppf quotient. Thus the cited statement really proves faithful flatness, rather than only topological surjectivity.

Step 6 checks the inverse diagonal on every algebra and gives inverse morphisms using projection and inversion. The commutation argument works on every scalar extension, as required by the stated meaning of central; no passage to the reduced kernel is used. This short functorial computation is elementary.

Step 7 uses exactly the subgroup-classification node's isomorphism to D(M) and its finite-dimensional clause. It is not enough to use the existing largest-subtorus node, since that node uses an embedding-based definition of multiplicative type. All citation quotes were copied verbatim from the new statements and rechecked as substrings. There is no uncited use of a proof internal to another node.

For the new statements I checked the trivial group, rank-zero torus and zero/nonzero representation boundary. The faithful representation can be made nonzero by adjoining a trivial line; hence its nonzero weight blocks cause no loss even for H=1. General affine-group image factorization is not restricted to smooth sources; smoothness is imposed only on the target for the rational-point converse. The derived-subgroup statement imposes both smoothness and connectedness before the rational-point generation clause. Semisimple-isogeny ascent assumes a finite scheme-theoretic kernel and smooth connected source, not an étale kernel. Diagonalizable subgroup classification includes mu_p in characteristic p. On the item, G=R gives D=1 and an isomorphism; R=1 gives a semisimple perfect group; G=GL_n with scalar R gives kernel mu_n, including nonreduced mu_n when the characteristic divides n. These cases agree with the formulas and show why reduced intersections would be wrong.

Each new node introduces its objects, has no proof sketch in its statement and no proof dependencies, and has actual searches. No proof step exceeds 2000 characters. The new nodes are general structural inputs; none restates this item's almost-product assertion or moves its proof into a single renamed clause. I corrected a draft source locator from the nonexistent 'Corollary 12.15' to Section 12.14 after rereading the PDF. The original mathematical statement required no correction. This is my author check; the maintainer still provides the independent review.

## Unfinished

None in this one-level split. The six new supporting statements are intentionally unsplit for subsequent stage-1 work.
