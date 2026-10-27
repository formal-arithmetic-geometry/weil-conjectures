# Q70: lem-sfb-infinite-field-semisimple-centralizer-reduction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-infinite-field-semisimple-centralizer-reduction.json: item, statement unchanged, split in eight proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-lie-additive-jordan.json: statement-only supporting lemma, unsplit; no Mathlib match. Algebraic-group membership and rational-representation compatibility go beyond Mathlib's linear Jordan decomposition.
- dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-derivation-zero-smooth.json: statement-only supporting lemma, unsplit; no Mathlib match. This is the local smoothness argument left implicit in Milne 17.76, formulated for derivations of smooth affine algebras.
- citations.json: every step/node pair, with verbatim statement quotations.
- report.md: this report.

## Attachments

None. Searched the live project WeilConjectures source by the exact blueprint id, noncentral/semisimple terms, centralizers and Jordan decomposition. The existing matrix-centralizer equations and tangent Lie-subalgebra declarations do not prove the rational existence, smoothness, connected identity component and nonunipotence required here. No Lean was written or compiled.

## WANTED

None: the source used is the local Milne Algebraic Groups PDF. Both new statements specify their exact relationship to Milne; the derivation version is agent-formulated rather than falsely attributed to a numbered theorem.

## Errors and gaps in the input/source

The item is mathematically correct and its statement is preserved. There was no supplied proof to retain. Milne 17.79 goes directly from a rational element with noncentral geometric semisimple part to a rational semisimple element. Its preceding Jordan decomposition is only stated over perfect fields. Taking that part as rational over an arbitrary infinite imperfect field would be unjustified. Step 3 supplies restricted p-power iteration instead: a sufficiently high p-power kills the matrix nilpotent part, stays in the rational restricted Lie algebra, and preserves a nonzero adjoint eigenvalue. Characteristic zero uses the rational Jordan decomposition. This preserves the source's intended conclusion and route without adding perfectness.

Milne 17.81 applies connected-group induction to C_G(X) without displaying the identity component. The given item's corrected identity-component formulation is retained: step 6 constructs C^0 and proves equality of its tangent space with that of C, before the dimension and nonunipotence arguments.

The phrase "all representations" surrounding Milne 17.74 must be understood here for rational algebraic group representations. An arbitrary representation of the abstract one-dimensional abelian Lie algebra may send a toral generator to a nontrivial Jordan block. The new Jordan lemma explicitly states rational algebraic representations and does not introduce that false abstract-Lie assertion. The item's faithful-matrix definition of semisimplicity is unchanged; faithful detection in the new lemma justifies its representation independence where used.

The supplied blueprint ancestry has from.node null, and blueprint_refs.py ancestor prints nothing. The inherited precise from.place and via chain are retained. New nodes prepend this item to that chain; no ancestor is invented. Read the current latest sk-thm-sf-ctf-stability-direct-images.proof.md (3), and searched the whole imported blueprint via blueprint_refs.py for Jordan, Lie Jordan, tangent dimension, smooth semisimple, semisimple derivation, additive Jordan and derivation zero. None states either new lemma or this item. The finite-type-group-identity-subgroup result is reused over arbitrary k rather than the existing algebraically closed identity-component node.

## Not duplicates

lem-sfb-algebraic-lie-additive-jordan vs lem-sfb-multiplicative-jordan-linear-compatibility: the latter concerns Jordan factors of group points and their linear/tensor compatibility; the new lemma concerns additive Jordan parts of tangent Lie elements, membership in the algebraic Lie algebra, and differentials of rational representations.

lem-sfb-algebraic-lie-additive-jordan vs lem-sfb-restricted-rational-differentiation: restricted differentiation supplies the p-operation and its representation compatibility in prime characteristic, but neither additive Jordan decomposition over perfect fields nor faithful detection in arbitrary characteristic.

lem-sfb-semisimple-derivation-zero-smooth vs lem-sfb-semisimple-fixed-subscheme-smooth: the latter is a fixed scheme of a semisimple group point over an algebraically closed field; the new lemma is the zero scheme of a derivation, including infinitesimal actions, over arbitrary k.

lem-sfb-semisimple-derivation-zero-smooth vs lem-sfb-torus-fixed-scheme-smooth: that lemma assumes an actual torus action and a representing fixed subscheme; an arbitrary geometric semisimple derivation, with possible characteristic-p eigenvalue relations, is not such an input.

lem-sfb-semisimple-derivation-zero-smooth vs lem-sfb-regular-quotient-parameter-approximation: that local-ring lemma assumes all parameter-ideal approximations; the new lemma constructs the applicable smooth zero scheme from a global geometric eigenspace decomposition and is not a specialization of those hypotheses.

lem-sfb-semisimple-derivation-zero-smooth vs lem-sfb-linearly-reductive-dense-fixed-smooth: that statement assumes a smooth linearly reductive algebraic group with a dense subgroup of rational points. A characteristic-p semisimple derivation may correspond to an infinitesimal diagonalizable action, with no such dense subgroup. No group action is assumed in the new statement.

## Review by Q70

I read Milne 17.74, Example 17.75 and Propositions 17.76–17.79 in the local PDF, and the semisimple-centralizer paragraph of 17.81, pp.377–379. For the Jordan node I checked the perfect-field hypothesis in 17.74 and wrote only the rational-algebraic representation version, with arbitrary-field faithful detection obtained after algebraic closure. For the derivation node I read the actual local parameter argument of Lemma 13.6 (p.256), its reference to Lemma 13.3 (p.255), and the sentence in 17.76 calling for its semisimple modification. The intended argument is to diagonalize D on every truncated local algebra at a zero, lift eigenvectors of m/m^2 to eigenvectors in every m/m^(n+1), and apply the regular-quotient parameter criterion. Nonzero eigenvectors generate the derivative ideal in each truncation, while the quotient is generated by zero eigenvectors. This is a genuine subsidiary smoothness lemma, not a restatement of a clause of the item. The new node has a statement only; this explanation is kept in the report.

Step 1 uses exactly affine-group-faithful-linear-representation for a closed embedding, and affine-group-dual-number-calculus for finite dimensionality, tangent injectivity and conjugation. I opened both statements. The matrix-unit computation proves diagonalizability of ad(S) directly, so no abstract Lie semisimplicity criterion is assumed. Determinant coefficients are actual polynomials over k. Step 2 writes out the infinite-field polynomial evaluation induction, including the constant-polynomial base case. It does not assume rational points on an arbitrary nonempty scheme.

Step 3 cites the newly stated additive Jordan lemma for perfect k or the algebraic closure, and the existing restricted-rational-differentiation statement. I checked that the latter states preservation of restricted powers under differentials and that its rational-coaction clause applies to the adjoint representation. Both branches preserve a nonzero eigenvalue; high p-powers are used only in positive characteristic. There is no descent of a Jordan part from an imperfect field.

Step 4 cites dual-number-calculus, which states the full adjoint action on all algebra-valued points and injectivity for closed subgroups. The stabilizer is defined by matrix equations on the universal G-matrix, not by its rational points. The dual-number calculation proves Lie(C)=ker ad(X) directly; C cannot equal G because this kernel is proper. Its finite-type affine structure is a quotient of the given coordinate algebra.

Step 5 uses the full new semisimple-derivation statement and dual-number-calculus, whose inner conjugation formula ensures that the ideal of G is D-stable. I checked the eigenvalues lambda_a-lambda_b, determinant weight zero, and that a D-stable ideal is a sum of eigenspaces by finite spectral projectors even in characteristic p. This checks exactly the new lemma's eigenspace hypothesis on the quotient algebra. The derivative ideal is the stabilizer ideal because both are generated by the commutator matrix entries and the determinant inverse has derivative zero. The lemma assumes geometric diagonalizability, so it applies over imperfect k without an unrecorded smoothness descent.

Step 6 uses the arbitrary-field finite-type-group-identity-subgroup statement, which explicitly makes the component open, closed, connected and a subgroup. I did not use the algebraically closed variant. The Mathlib leaf open-immersion-smooth-composition gives smoothness of K; the open-factorization node gives the inverse bijection on tangent vectors, since a dual-number scheme at e has only that underlying point. Closed immersion, affineness and finite type are successive quotient-ring statements already contained in the defining closed-immersion notion.

Step 7 opens and cites the full statements of smooth-lie-local-dimension and group-identity-local-dimension. The former says arbitrary field and smooth group; the latter says arbitrary field and finite-type group, with no reducedness assumption. K and G satisfy both. Their equalities give global dimensions from the proper tangent kernel, by an explicitly described basis extension. These are declared off-unit generic dimension tools, not a substitution of a different route for the unit's proof. The open-factorization node is declared as a generic tool too.

Step 8 tests X in Lie(K) by [X,X]=0. If K embeds in U_n, its tangent image is strictly upper triangular and hence nilpotent. The new Jordan node's arbitrary-field faithful detection transfers nilpotence to the original G-embedding restricted to K; that image is already diagonalizable. Its vanishing contradicts X being noncentral and tangent injectivity. This checks the representation issue rather than assuming that semisimplicity in one faithful embedding is automatically compatible with a different embedding.

I tested the statements on the trivial group, G_m, G_a, diagonal matrix groups, GL_2, a diagonal-plus-nilpotent matrix and its high p-powers, and the imperfect field F_p(t). Abelian/trivial groups cannot meet the noncentral hypothesis. The derivation lemma permits D=0 (I=0), D(x)=x (zero scheme x=0), characteristic-p Euler derivations with weight-zero pth powers, and an empty zero scheme. No claim about connectedness of the whole centralizer was introduced. Each new node is strictly subordinate: one provides algebraic Jordan structure; the other provides a general derivation zero-scheme theorem, while the item's steps still construct X, C, K and prove all reductions. No step exceeds 2000 characters, and no whole item clause has been moved into a replacement node.

For Mathlib I read the logged search outputs and inspected LinearAlgebra/JordanChevalley.lean (the linear existence/uniqueness theorems) and Algebra/Lie/AdjointAction/JordanChevalley.lean. Those do not give algebraic-group Lie membership or rational representation compatibility. The other returned declarations are manifold Lie constructions, abstract Cartan/regular Lie elements, smooth loci or standard-smooth algebra criteria. Each new node has real leanfinder, loogle, grep and leansearch records, with a second natural-language phrasing, and no unavailable service is recorded as absence. The searches and their logs have not been fabricated. No new Mathlib leaves were identified.

## Unfinished work

Only the two newly created statement-only lemmas remain unsplit, as required for a one-level split. No unresolved mathematical objection to the item remains. Required dry run and delivery results will be recorded below.
