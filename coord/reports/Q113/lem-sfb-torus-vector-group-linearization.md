# Stage-1 delivery: lem-sfb-torus-vector-group-linearization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-vector-group-linearization.json: split item, five proof steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-vector-group-additive-polynomials.json: new statement-only lemma; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-equivariant-frobenius-module-basis.json: new statement-only lemma; no Mathlib match.
- citations.json: verbatim supporting statements for all six step/node citations.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, vector group, vector-group, torus action, torus/linearization, additive polynomial and homogeneous basis. No declaration states the item. The homogeneous bases in RingTheory/GradedNakayamaFree and MinimalGradedPresentation concern commutative graded rings, not the Frobenius skew ring. The imported item has no finished Lean attachment.

## WANTED

WANTED: Conrad--Lichtenstein, Linear Algebraic Groups I, Appendix D.3, proof of Theorem D.3.2, printed pp.86--87, for lem-sfb-torus-vector-group-linearization. Read the PDF online at https://math.stanford.edu/~conrad/252Page/handouts/alggroups.pdf; this document is not in the local literature directory. No download or repository edit made.

WANTED: Conrad--Gabber--Prasad, Pseudo-reductive Groups, Appendix B.4, especially Theorem B.4.3, for the literature behind lem-sfb-torus-equivariant-frobenius-module-basis. Not read and not claimed as a verbatim statement of that theorem. The new lemma is agent-formulated algebra, with a full justification below. No SGA source is used.

## Corrections and scope

The original statement is true, including arbitrary fields and characteristic p. There is no STATEMENT-DISPUTED correction. Its source.document is Milne while its source.place describes the Conrad notes and requests them locally; I retain that inherited record, explicitly distinguish these sources here, and mark the proof origin agent. The proof does not pretend that Milne Proposition 14.50 asserts a homogeneous basis. It uses a new graded refinement with its own independent hypotheses. The characteristic-zero case needs no coordinate change; the positive-characteristic case requires additive polynomial coordinates. For example, conjugate diag(t,t) by (x,y) -> (x,y+x^p): the resulting action has a y-coordinate term (t^p-t)x^p, so its original coordinates need not be linear.

The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3), and the chapter and unit records were read. This is a deep supporting algebraic-group input in the existing ancestry, not a change to the constructibility route. blueprint_refs.py ancestor prints None; the inherited from.node=null and the full existing via list are retained. New nodes add this item to via and identify their precise role. Searches of the entire imported blueprint for vector group, additive polynomial, homogeneous basis, Frobenius skew, primitive and weight found no matching blueprint statement. No unit or chapter file changed.

## Not duplicates

lem-sfb-vector-group-additive-polynomials vs lem-sfb-primitive-frobenius-module-duality: reconstruction identifies a group with U(P(G)); it does not classify P(G_a^d) as a free module with coordinate basis, nor state the characteristic-zero classification. The primitive functions calculated in its proof are not its statement.

lem-sfb-vector-group-additive-polynomials vs lem-sfb-smooth-p-torsion-additive-embedding: the latter embeds a smooth exponent-p group into a vector group; it does not classify additive polynomial functions.

lem-sfb-vector-group-additive-polynomials vs lem-sfb-additive-subgroup-perfect-decomposition: the latter classifies subgroups over perfect fields; the new lemma classifies polynomial identities over arbitrary fields, including characteristic zero.

lem-sfb-torus-equivariant-frobenius-module-basis vs lem-sfb-frobenius-skew-free-submodules: ungraded freeness of a submodule does not give a basis in specified weight spaces. Here the whole module is already free and the conclusion controls the grading.

lem-sfb-torus-equivariant-frobenius-module-basis vs lem-sfb-connected-graded-projective-free: the latter assumes a commutative connected graded algebra with additive degrees. Here A is generally noncommutative and F sends weight nu to p nu, not nu plus a fixed integer.

lem-sfb-torus-equivariant-frobenius-module-basis vs lem-sfb-graded-nakayama-connected: that lemma is again for a commutative algebra with additive grading and provides generation, not a free homogeneous basis for a Frobenius-skew action.

lem-sfb-torus-equivariant-frobenius-module-basis vs lem-sfb-gm-representation-weight-basis: that node starts with a finite-dimensional linear representation and has no skew-module or nonlinear-coordinate assertion.

lem-sfb-torus-equivariant-frobenius-module-basis vs lem-sfb-torus-vector-group-linearization: the new node is a purely module-theoretic freeness statement with an assumed direct-sum grading. It neither produces a grading from a scheme action nor constructs an additive-polynomial isomorphism, an inverse, or a group-scheme representation. Those are steps 1, 4 and 5 of the item. Thus the geometric content is not moved into a restatement.

No Stacks tag is asserted for these specialized algebraic-group/Frobenius-module results. DAG searches covered key phrases, Milne 14.40, 14.50, and Conrad D.3.2. Existing nodes using the same Milne paragraphs have been distinguished above. Sources for general scheme facts are not substituted for these claims.

## Arguments retained for the new statement-only nodes

For additive polynomials, I read Milne Example 14.40, equations (95)--(97), printed pp.292--293, in the local PDF (pdftotext output is in this sandbox). Additivity applied to the sum of coordinate-axis vectors gives f(X)=sum_i f_i(X_i); f(0)=0. In characteristic zero, a nonzero coefficient in degree n>1 would contribute the nonzero coefficient n times that coefficient to X Y^(n-1) in f(X+Y), a contradiction. In characteristic p write n=p^r m with p not dividing m. If m>1, the coefficient of X^(p^r)Y^(p^r(m-1)) in (X+Y)^n is m, nonzero, because (X+Y)^n=(X^(p^r)+Y^(p^r))^m. Distinct n have distinct total degrees, so no cancellation between them is possible. Thus only p-power exponents survive, and conversely these powers are additive. The coordinate monomials are linearly independent as formal polynomials, even over finite fields. This proves the displayed direct sums. Composition of the operators c F^r gives exactly c b^(p^r) F^(r+t), and hence the x_i freely generate the left A-module. This is more than a short invocation of definitions; the coefficient classification is the independent lemma.

For the homogeneous-basis lemma, I read Milne Proposition 14.50 and its preceding division-algorithm paragraph, printed p.296, as well as the Conrad vector-group paragraph online. The following is my algebraic proof, not a claim that either paragraph states it verbatim. Let M_0 be the zero-weight submodule and N=sum_{nu!=0} M_nu. Both are A-submodules, since p nu=0 iff nu=0, and M=M_0 direct-sum N. They are finitely generated, being images of the A-linear projections of finite generators of M; Milne 14.50 makes each free. An A-basis of M_0 is automatically homogeneous. Split the finite generators of N into their homogeneous components. Those finitely many components still generate N. Consequently its weights lie in finitely many sets {p^r nu_i : r>=0} with nu_i nonzero.

Write JN for the k-span of F(N), not the bare semilinear image, which need not be a k-subspace over an imperfect field. If (e_i) is an A-basis of N, its k-basis is (F^r e_i)_(r>=0,i). Therefore the linearization k tensor_(k,sigma) N -> N, a tensor n -> a F(n), is injective, with image JN; in the displayed basis it shifts r to r+1. In particular N/JN is finite-dimensional with dimension the A-rank of N. JN is graded because F multiplies the weight by p. Choose a homogeneous k-basis of N/JN and homogeneous lifts b_i. Let L be their span, so N=L direct-sum JN as k-vector spaces.

These b_i generate over A. For a nonzero integral lattice vector nu define h(nu) as the largest r such that p^r divides every coordinate. The finitely many generating weights give a common lower bound for h on the support of N. Reduce a homogeneous element modulo JN to L. The remainder is a sum of c F(n) with n homogeneous of weight nu/p. When this weight exists h decreases by one; when nu is not divisible by p the remainder is zero. Recursion terminates at the support bound and expresses the element using the b_i and their Frobenius iterates. No p-th root of a coefficient is taken.

They are independent as well. Apply the injective Frobenius linearization to N=L direct-sum JN; extension of scalars along the field map sigma preserves a direct sum and bases. Thus JN=(k-span F(L)) direct-sum (k-span F^2(N)). Repetition shows that, for every r, the spaces spanned by L,F(L),...,F^(r-1)(L) are independent; each has basis the corresponding F^j(b_i). A finite A-linear relation is a finite k-linear relation between these independent vectors and hence is zero coefficient by coefficient. This proves a homogeneous A-basis of N. Together with the basis of M_0 it is a basis of M. Its size is d: for any finite A-basis the quotient M/(k-span F(M)) has k-dimension its size, and for the given A^d this dimension is d. This argument covers zero weight, not just strictly positive weights, and does not assume k perfect.

## Mathlib search results

Every search in the new node JSON was run by the required msearch.py command and is in this item's searches.jsonl. The initial conceptual searches and a second, more precise formulation were read before deciding there was no match. The records preserve exact query text and actual result digests. The first Loogle query with an unknown GradedModule identifier was not used as evidence; valid queries Module.Basis, "homogeneous" and quoted name searches were also made. Both semantic services were available for the recorded searches. No matching leaf was found.

I read Mathlib/Algebra/SkewPolynomial/Basic.lean: SkewPolynomial is the ring itself, not the graded-basis theorem. SkewMonoidAlgebra's coefficient basis makes the ring free over k, not an arbitrary graded module free on homogeneous elements. GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous is a finite-generation statement about a commutative graded algebra. LinearMap.toMvPolynomial_isHomogeneous starts with a linear map and has no Frobenius-module conclusion. Polynomial.addHom_ext concerns homomorphisms out of the polynomial additive group. MvPolynomial.expand_char supplies a Frobenius substitution identity, not the classification of all additive polynomials. DistribMulAction.toModuleAut assumes commutation with scalar multiplication, which is precisely unavailable for the original nonlinear action. None is an exact match or a one-line specialization.

## Review by Q113

I checked the whole B--E checklist with the three JSON files and cited source passages open. I read the item against the Conrad D.3.2 vector-group paragraph, which treats characteristic zero and, in characteristic p, separates a trivial-action factor from a linearly acted vector factor. I read Milne 14.40 and 14.50 for the two new nodes; their generalizations and my arguments are distinguished above. The new nodes have complete independent statements, all rings, actions, gradings and polynomial identities defined inline, and only a field-definition dependency. Their proof fields are empty. Neither is a target clause repackaged as a geometric linearization theorem, neither is a two-line elementary fact, and the related DAG statements have been read and distinguished under Not duplicates.

Step 1 uses the additive-polynomial node's explicit space P_d; comparing Laurent coefficients proves both preservation and the direct-sum decomposition, rather than citing a finite-dimensional weight theorem on an infinite-dimensional module. Step 2 uses exactly its characteristic-zero equality P_d=sum kx_i. That equality makes the action matrix linear over any k-algebra; inversion is supplied by the action of e^-1, with no reliance on k-points being dense. Step 3 uses exactly its free left A-basis assertion and exactly the new basis lemma's homogeneous-basis assertion. I verified prime positive characteristic, finite rank d, finite torus rank s, k-linear weight subspaces, internal finite decompositions and F multiplying weights by p. Step 4 uses the first node's interpretation of A as additive polynomial operators. The explicit inverse basis-change polynomial is written out, so the proof does not confuse a separable additive isogeny with an isomorphism. Step 5 uses only the previously established identities; it constructs rho and a and verifies equivariance and both coaction identities on every algebra, including algebras with nilpotents. All cited statements say what those steps take, and citations.json copies the corresponding sentences verbatim.

The subtle hypothesis check was imperfectness: I corrected the prospective auxiliary argument to use k-span(F(N)) and the injective linearization of F, not the possibly non-k-linear image F(N), and separated weight zero before the bounded-weight recursion. The final statements require no perfection or algebraic closedness. Small cases: d=0 is the zero polynomial space and empty basis; s=0 gives only degree zero and any original basis works; the rank-one weight-nu module has F^r of weight p^r nu; all-zero weights reduce to ungraded freeness; k=F_p(t) satisfies the argument despite nonsurjective Frobenius; k=F_p and the polynomial X^p-X illustrate why all assertions concern formal polynomial identities rather than functions on k-points. The conjugated triangular example above tests the need for nonlinear additive coordinate changes. Positive-characteristic polynomial inverses, not merely bijections on fields, are used. No step exceeds 2000 characters, and the module-basis argument is isolated rather than hidden in a long geometric step. No off-unit theorem is cited and no cycle is introduced.

## Unfinished work

No part of the one-level split remains unfinished. The two statement-only algebraic prerequisites remain unsplit for subsequent workers, with their full arguments recorded above. This delivery writes no Lean, runs no compiler or Lake, makes no changes to the shared repository or launcher, and starts no agents. Required server dry run and push follow this report.
