# Q77: lem-sfb-triangular-group-representation-eigenline

## 1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-triangular-group-representation-eigenline.json: existing statement, now split into eight steps. The statement and statement dependencies are unchanged. Mathlib verdict: no match.
- citations.json: a verbatim statement excerpt for every proof-step citation.
- report.md: this report.

There are no new nodes and no new Mathlib leaves. searches.jsonl is the search command's original log. write_split.py is sandbox preparation material, not a DAG delivery file.

## 2. Attachments

None. Searching lean/WeilConjectures for the blueprint id, triangular/trigonalizable groups, eigenline/eigenvector, rational representations and comodules found no declaration stating this item. The existing source tensor-family lemma is reused through its DAG node; it is not an attachment for the item.

## 3. Wanted literature

None. All mathematical sources used are in the supplied Milne PDF or existing project source. No SGA source is used.

## 4. Findings and changes

The item had no proof. Milne Proposition 16.2 proves (c) implies (d) implies (a), not a direct Lie-algebra argument. I followed precisely that route. The triangular-diagonal-kernel node states the kernel and quotient geometry, but also brings in stronger section claims that are unnecessary here; its underlying arbitrary-field affine-image factorization is the smaller existing input actually used. The smooth, algebraically-closed-field fixed-vector node is insufficient: I instead used the existing unitriangular-subgroup-rational-fixed-vector node, whose hypotheses allow nonreduced group schemes and arbitrary fields. Likewise the split-torus-subgroups-diagonalizable node assumes an algebraically closed field, and the torus weight node concerns tori rather than arbitrary closed subgroup schemes. Step 6 writes Milne's short Laurent-monomial/group-like argument directly, using the existing coalgebra independence lemma; it does not apply either of these mismatched nodes.

The latest blueprint (literature/blueprint/latest, main-20261024) direct-images proof (3), chapter and ctf unit were read. This is a deep supporting representation-theoretic input along the inherited alteration route, not the unit key statement; no unit realization record was changed. blueprint_refs.py ancestor returns None for this created-node chain, consistent with the inherited blueprint.from.node=null. I retained that provenance and filled the split_report explanation. Blueprint searches for trigonalizable, diagonalizable, eigenline, eigenvector, faithful, tensor powers, normal subgroup and coconnected found no equivalent blueprint assertion. The Lie-algebra common-eigenvector nodes have different objects, characteristic and field hypotheses.

All seven new searches were actually run through the required msearch.py command, read, and recorded in addition to the inherited search records. Two semantic phrasings found abstract-group Schur/irreducibility results, not rational group-scheme assertions. Loogle's Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative was read at Mathlib/RepresentationTheory/Irreducible.lean:73--90: it requires IsAlgClosed and a commutative abstract monoid. The LieModule.IsTriangularizable definition at Algebra/Lie/Weights/Basic.lean:702--705 concerns individual Lie-algebra endomorphisms. Representation.invtSubmodule.nontrivial_iff at RepresentationTheory/Submodule.lean:51 concerns the lattice of invariant subspaces (containing zero and the whole space), not existence of a one-dimensional invariant subspace. None is a match or one-line specialization of this item. No search is reported as unavailable; all returned successfully.

## 5. Unfinished work

None for this one-level split. Existing dependencies retain their own stage states.

## Not duplicates

No new nodes were created. Searches of the whole DAG by statements, source places 16.2, 14.5, 12.9/12.12 and notions identified the existing input nodes; all are reused. No new-vs-existing pairs require adjudication.

## Review by Q77

I read Milne, Algebraic Groups (2017), printed pp.324--325 (Definition 16.1 and the actual proof of Proposition 16.2), pp.281--282 (14.5, including its scheme-theoretic fixed-vector meaning), pp.234--235 (12.9(c) and the coefficient proof of 12.12), p.102 (5.15), p.101 (5.13), p.75 (3.34), p.84 (representation/comodule dictionary), and p.93 (group-like independence). There are no new nodes requiring additional sources. For the tensor-family input I also read the existing project proof at lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basis.lean:24--48. All cited node statements were opened and read; citations.json uses actual substrings rather than paraphrases.

Step 1 uses the affine-image factorization for arbitrary affine finite-type groups, not its smooth/algebraically-closed variant. The target torus and the source J satisfy these hypotheses. The G_m node supplies the torus factors. The closed-immersion node gives affine quotient equations; imposing diagonal=1 on J produces a finite-type closed subgroup of the unitriangular group. The kernel equality follows from the closed immersion of the image, pointwise over every algebra, and normality is the explicit kernel computation. No smoothness of this kernel is asserted.

Step 2 uses the dictionary to turn the stated coaction into a group-scheme representation and restrict it. The fixed-vector node says exactly that a nonzero finite-dimensional representation of a closed unitriangular subgroup has a vector fixed over EVERY algebra, with no smoothness or field-splitting hypotheses. Choosing a basis gives its k^d form. Evaluating at the universal N-point gives membership in W=ker d; mere k-point invariance would not suffice.

Step 3 supplies the invariant base-extension test that Milne 5.15 uses. The dictionary supplies the universal-point evaluation formula. The tensor-family node really states zero detection after tensoring any jointly injective family with any k-vector space. Its singleton specialization applies to d restricted to a vector-space complement of W; it has no finite-dimensionality requirement on k[N] or R. The explicit direct-sum decomposition identifies the kernel after tensoring. This is a short calculation from that statement, so I did not invent a separate kernel/base-extension node.

Step 4 is the written conjugation calculation in Milne 5.15. Normality is scheme-theoretic and therefore holds over R' for every extension of R, exactly what Step 3 needs. Applying g inverse proves automorphism, not just preservation. The dictionary gives a rational subrepresentation from the natural restrictions and gives the inclusion's coaction identity. This short calculation is marked elementary with the dictionary cited; it invokes no unnamed invariant-submodule theorem.

Step 5 applies precisely the quoted quotient-universal statement: q is faithfully flat on coordinate algebras, N is its scheme kernel, and the representation on W kills N as a morphism of group schemes. I checked GL(W) is affine of finite type using the general-linear-group node's localization presentation (W is nonzero by Step 2). Thus all three groups in the universal statement have the required hypotheses. The final coaction formula is checked at the universal point using the dictionary, not assumed from pointwise descent over k.

Step 6 uses the affine closed-immersion characterization to obtain a SURJECTION from the torus Laurent algebra. The Laurent-ring definition gives finite monomial expansions; iterating its one-variable presentation represents n independent units. The G_m Hopf formulas and affine-group-coordinate-hopf statement give group-like images of every Laurent monomial. Their counits are 1, so no image is zero even in positive characteristic. The coalgebra independence statement concerns distinct group-like elements over ANY field, so their distinct spanning images form a basis. This proves exactly the part of Milne 12.9(c) needed here, without silently borrowing the algebraically-closed version of a different node. Inverse monomials prove the images are units.

Step 7 is the two displayed coefficient identities of Milne 12.12, written out. Expansion in the established group-like basis and applying its coefficient functionals to the last factor are elementary linear algebra. The counit sum shows a nonzero coefficient exists; coassociativity makes it an actual eigenvector, not a generalized eigenvector. It is not a new node restating the item.

Step 8 constructs the character, rather than asserting that a scalar function must be one. The multiplicative-group node supplies its Laurent Hopf presentation; the coordinate-Hopf node's antipode identity gives S(e_i)=e_i inverse. Thus multiplication, identity and inverse are all respected. The dictionary then evaluates the coaction formula after every algebra extension, giving every clause of the item. During this self-check I made the inverse-compatibility justification and the GL(W) finite-type check explicit, and added their precise citations.

I checked delivery-errors B--E against these files: no new statements, duplicates, hidden clause-nodes, fabricated searches, unquoted citations or dependency cycles. I traversed the statement/proof dependency closures of the chosen inputs and none reaches this item. The eight proof steps are each below 2000 characters (the longest is below 1000); the kernel-complement and coefficient calculations are routine arguments from the explicitly cited inputs, not omitted standard lemmas. The statement introduces the required notions inline and its statement dependency list was preserved. Existing import/provenance fields were retained.

Small cases: n=1 has trivial unitriangular kernel, so W=V and the quotient is a closed subgroup of G_m; a trivial J gives the trivial monomial character. For diagonal mu_p in characteristic p the distinct monomial images are still linearly independent group-like elements although the coordinate algebra is nonreduced; the argument never uses geometric-point density. For alpha_p or a finite constant p-subgroup of U_n the nonsmooth/arbitrary-field unitriangular input applies and the quotient can be trivial, giving a fixed line. Over a finite or imperfect field the Hopf/coefficient calculations and the cited arbitrary-field lemmas still apply. V=0 is expressly excluded; dim V=1 needs no induction and is included. No algebraic closure, characteristic-zero, smoothness, connectedness, reducedness, or pointwise-surjectivity hypothesis was added.

Dry-run repair: the citation checker required a longer quote for the GL(W) affine finite-type check. I expanded that citation to include the field, polynomial algebra, determinant and localization formula A=P[1/D]. No proof or statement changed.
