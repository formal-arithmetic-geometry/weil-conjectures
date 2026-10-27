# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-restricted-symmetric-basis.json: item, statement unchanged, six proof steps, split.
- dag/nodes/sec-six-functors-basics/lem-sfb-symmetric-algebra-monomial-basis.json: statement, Mathlib leaf Module.Basis.symmetricAlgebra, arbitrary index type.
- citations.json: one verbatim statement excerpt for every use in every proof step.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the semilinear/restricted symmetric-algebra and restricted-enveloping notions. The symmetric-algebra project files concern localization, sheaf charts and cotangent complexes, not this quotient basis. No project declaration states the item.

## WANTED

None. Milne's Algebraic Groups iAG2017 PDF is present and was read locally.

## What was wrong or missing

The item was an accurate statement-only prerequisite. There is no statement dispute. Existing lem-sfb-restricted-pbw-basis and lem-sfb-field-filtered-pbw both assume finite-dimensional Lie algebras. They cannot be applied to an arbitrary semilinear endomorphism by claiming finite-dimensional invariant subspaces. Instead I expanded Milne Theorem 10.40's mixed-monomial proof in the commutative algebra itself. The new node is only the unrestricted ordinary symmetric-algebra basis; it does not restate the quotient basis or injectivity clause.

The inherited blueprint.from.node is null. tools/blueprint_refs.py ancestor reports None for this item as well. I retained that ancestry and the inherited via list; from.place already describes the exact Milne 10.40/14.43 input. I read the current latest unit and direct-images proof (3), not an older snapshot. This algebra calculation is far below the unit route and does not change it.

## Not duplicates

lem-sfb-symmetric-algebra-monomial-basis vs lem-weil-pbc-symmetric-algebra-free-module-polynomial: the existing statement treats the finite standard free module R^{oplus n}; the new leaf treats every basis of an arbitrary vector space and explicitly states the monomial basis. The existing Mathlib match is more general than its natural-language statement, but C4 forbids extracting that stronger statement from the existing node.

lem-sfb-symmetric-algebra-monomial-basis vs lem-sfb-field-filtered-pbw: the existing statement is for finite-dimensional possibly nonabelian Lie algebras and their ordinary enveloping algebras. Its finite-dimensional hypothesis excludes the arbitrary-index assertion needed here.

lem-sfb-symmetric-algebra-monomial-basis vs lem-sfb-tensor-word-basis: the existing leaf gives all ordered words in the noncommutative tensor algebra, not the commutative monomials in the symmetric algebra.

lem-sfb-symmetric-algebra-monomial-basis vs lem-sfb-restricted-pbw-basis: the existing node concerns the restricted enveloping quotient of a finite-dimensional restricted Lie algebra. The new leaf concerns the unrestricted symmetric algebra of any vector space, before imposing any p-relations.

Whole-DAG statement searches for symmetric algebra with basis/monomial/polynomial, and the whole-blueprint searches `restricted`, `symmetric algebra`, and `monomial basis`, found no equivalent existing node. The same-source Milne restricted-PBW nodes were read, not used as if they allowed arbitrary dimension. No Stacks tag is asserted in this delivery: the applicable source is Milne and the new leaf has its Mathlib file and lines.

## Review by Q68

For the item I read Milne Definition 10.39 and Theorem 10.40, printed pp.206-207, including the full proof about central elements c_i, the mixed basis and the quotient. The theorem explicitly permits an arbitrary ordered basis. I also read Lemma 14.43, printed p.294: its application uses an arbitrary k-basis even though the module is finitely generated over the Frobenius operator ring. I do not take its finite operator-generation assumption as a vector-space finiteness hypothesis. The proof here works directly in the symmetric algebra, so no noncommutative PBW or restricted-Lie axioms have been silently assumed. No SGA source is used.

For the new leaf I read Mathlib/LinearAlgebra/SymmetricAlgebra/Basis.lean:49-77 and Mathlib/RingTheory/MvPolynomial/Basic.lean:203-209. Module.Basis.symmetricAlgebra at line 74 is precisely the transported monomial basis. equivMvPolynomial at line 49 and its generator formula at line 58 show that the transported vector is the claimed product. No finite type or finite-dimensional instance occurs in these declarations. The new statement is self-contained and needs only the field and symmetric-algebra definition nodes. The required semantic, Loogle, LeanSearch and grep searches all ran through msearch.py and their results were read. Searches about the item used two semantic phrasings; all hits give unrestricted bases, ordinary enveloping algebra constructions or unrelated Frobenius field bases, not the quotient assertion. Existing search records on the imported item are preserved; newly added entries use exactly the logged queries.

Step 1 uses the new leaf's explicit ordinary monomial basis. I checked that its statement allows arbitrary I. The degree subspaces are defined here in coordinates; multiplicativity is the written identity E^m E^n=E^{m+n}, and Te_i is an actual vector with finite coordinate support.

Step 2 uses the full commuting binomial formula in lem-sfb-commuting-binomial-expansion, whose statement was opened, and the inverse axiom in def-weil-field, whose statement was also opened. The ambient S is commutative by the item's symmetric-algebra definition, so the commuting hypothesis holds. The prime-characteristic assumption makes 1,...,p-1 nonzero. The displayed binomial identity therefore proves the vanishing of all intermediate coefficients. Applying additivity and semilinearity to a finite basis expansion gives precisely the displayed generator relation; I checked both inclusions of the relation ideals. This is a short calculation, not an appeal to an uncited Frobenius theorem.

Step 3 expands finite products of the defined c_i; it needs no external result. Every lower term loses at least p-1 in ordinary total degree, since Te_i has degree at most one and p>=2. Division with remainder preserves finite supports. This is the elementary leading-term calculation from Milne's proof, with all its hypotheses made explicit.

Step 4 uses the new leaf again for coefficient independence of ordinary monomials. I wrote both the strong induction giving mixed spanning and the finite maximal-degree contradiction giving mixed independence; it does not cite an unproved triangular-basis lemma. The argument involves finitely many terms in each expression, even though degree pieces can have infinite dimension. Every lower-degree term genuinely has smaller natural-number degree, so the induction is not circular.

Step 5 uses the opened def-weil-pbc-algebra-hom-quotient for the exact quotient kernel and surjective map. The ideal-span identification is proved by expanding an arbitrary finite sum f_i c_i in the already established mixed basis and by factoring each mixed vector with b!=0 by a c_i. Commutativity is in force. The disjoint-coordinate argument explicitly proves both quotient spanning and independence; it does not assume the desired quotient basis.

Step 6 needs no new theorem: p>=2 makes unit multiindices allowable; a finite coordinate expansion then proves injectivity. The empty-basis case is handled explicitly. This generalizes the injectivity reasoning of Milne Corollary 10.41 directly, rather than dropping that corollary's finite-dimensional hypothesis by citation.

Small-case checks: V=0 gives k with basis 1. For one basis vector, T=0 gives k[x]/(x^p), while T(e)=lambda e gives k[x]/(x^p-lambda x), both with the stated p monomials, including p=2. Over the nonperfect field F_p(t), taking T(e)=t e uses only a_i^p and never a pth root. For I=N, T(e_i)=e_{i+1} extended semilinearly gives a non-locally-finite operator; the mixed comparison still uses only finite supports, even though T introduces new indices. These checks verify the absence of hidden perfectness, nilpotence or invariant-subspace assumptions.

I checked delivery-errors B through E against the files: the sole new node is a genuine Mathlib leaf with no proof, complete notions, correct TeX and verified lines; no added node duplicates the item or its clauses. Each cited statement is quoted verbatim in citations.json. Every non-elementary input is cited; all remaining steps are explicitly written finite expansions, coordinate arguments or natural-number induction. All proof steps are under 2000 characters. The original statement and its statement dependencies are unchanged, so no hypotheses were weakened or added. There are no off-unit non-Mathlib tool citations and no cycles introduced by the new leaf.

## Unfinished work

None in the proposed stage-1 split. Delivery is subject to the required server dry run and push.
