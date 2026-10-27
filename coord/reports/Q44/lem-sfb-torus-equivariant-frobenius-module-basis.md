# Stage-1 delivery: lem-sfb-torus-equivariant-frobenius-module-basis

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-equivariant-frobenius-module-basis.json: split item; five proof steps, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-coefficient-endomorphism-preserves-independence.json: statement-only algebra lemma; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-dilating-weight-nakayama.json: statement-only semilinear generation lemma; no Mathlib match.
- citations.json: exact statement quotations for the three step/node citations.

## Attachments

None. Read-only searches in lean/WeilConjectures for the exact blueprint tag, Frobenius/basis in both orders, torus basis, skew polynomial, semilinear independence, and dilating weight/Nakayama found no declaration stating the item or either new node. The field-theory FrobeniusBasisCompositum and fixed-points lemmas concern field extensions or fixed vectors, not the objects here. SemilinearFrobenius.lean was inspected for that distinction. No source writing or compiler invocation took place.

## WANTED

WANTED: Conrad--Lichtenstein, Linear Algebraic Groups I, Appendix D.3, proof of Theorem D.3.2, p.86, for the geometric motivation of lem-sfb-torus-equivariant-frobenius-module-basis. Not locally available and not read in this session.

WANTED: Conrad--Gabber--Prasad, Pseudo-reductive Groups, Appendix B.4, for the homogeneous refinement behind that paragraph. Not locally available and not asserted as a source of a verbatim theorem. No download performed and no SGA source used.

## Corrections and scope

The statement is unchanged. Its hypotheses are sufficient over imperfect fields. The source record mentions the unavailable geometric sources, but the present proof is explicitly agent-written. I read local Milne Proposition 14.50 and the preceding division algorithm, printed p.296 (PDF page 308), and the existing node lem-sfb-frobenius-skew-free-submodules. Milne states ungraded freeness, not a homogeneous refinement. That distinction is maintained. The parent report coord/reports/Q113/lem-sfb-torus-vector-group-linearization.md was read as material; its proof strategy is retained, with the two genuine algebraic subclaims isolated below instead of hiding a semilinear independence argument.

The item has no lean_audit field or Lean declaration. There is no released repair note and no prior sandbox split/report to resume. Inherited Mathlib searches are retained; the new searches are also recorded literally from this sandbox's searches.jsonl. The current latest blueprint unit and direct-images proof clause (3), its chapter record, and the stored unit record were read. The inherited blueprint ancestor is null and blueprint_refs.py ancestor prints None. That existing ancestry and precise place are retained; the children prepend the item to via and add the exact supporting argument. No chapter or unit record changed.

## Not duplicates

lem-sfb-coefficient-endomorphism-preserves-independence vs lem-sfb-torus-equivariant-frobenius-module-basis: the new lemma has no weight decomposition, operator, skew module, generation, or basis assertion; it controls only finite independent coordinate vectors under an arbitrary field embedding.

lem-sfb-dilating-weight-nakayama vs lem-sfb-torus-equivariant-frobenius-module-basis: the new lemma asserts generation only, for arbitrary semilinear vector spaces with no zero weight and no freeness hypothesis; it gives neither independence nor a basis and cannot handle the zero-weight summand.

lem-sfb-dilating-weight-nakayama vs lem-sfb-graded-nakayama-connected: the existing node assumes a commutative connected graded k-algebra and additive degree shifts; the new one concerns a semilinear operator dilating lattice weights. It does not follow by substituting into the existing assumptions.

lem-sfb-dilating-weight-nakayama vs lem-sfb-connected-graded-projective-free: the latter is a homogeneous basis theorem for projective modules over commutative connected graded algebras, with additive degrees; neither its algebra hypotheses nor its conclusion are those here.

lem-sfb-coefficient-endomorphism-preserves-independence vs lem-sfb-frobenius-skew-free-submodules: ungraded submodule freeness does not assert coordinatewise preservation of k-linear independence under arbitrary field embeddings. The latter existing node is cited, not recreated, for the zero-weight and nonzero-weight free summands.

lem-sfb-dilating-weight-nakayama vs lem-sfb-frobenius-skew-free-submodules: generation from a quotient of a possibly nonfree semilinear space is different from freeness of finitely generated submodules.

Searches used the entire DAG and blueprint: skew polynomial, homogeneous basis, semilinear, scalar extension basis, coefficientwise, injective field, Frobenius independent, Nakayama. The possible graded Nakayama and projective-free statements were opened and read. Keyword searches also covered the live Lean source. No Stacks tag is asserted for these agent-formulated algebra lemmas, so there are no shared-tag pairs to excuse. The ordinary field definition is reused.

## Arguments for the statement-only prerequisites

For lem-sfb-coefficient-endomorphism-preserves-independence, all finitely many vectors have support in a finite set S. Arrange them as columns of a matrix C over k. Independence means column rank m, so Gaussian elimination selects m rows giving a square minor D of nonzero determinant. Equivalently Gaussian elimination of C has m pivots, and the pivot rows select such a minor. Under coefficientwise sigma the same minor has determinant sigma(det D), by the finite alternating-sum determinant formula; this is nonzero because sigma is injective. Thus its columns, and consequently the full transformed columns, are independent over k. No inverse to sigma and no roots of coefficients occur. This is the general coordinate-embedding algebra lemma, not a statement about field elements raised to a power inside an extension. The finite-rank/minor argument is substantive enough to keep as its own statement-only node; no proof was written into its JSON.

For lem-sfb-dilating-weight-nakayama, J is homogeneous: decompose each input to T into its finitely many homogeneous parts and group the outputs by weight; multiplication by p on the lattice is injective. Thus J intersect V_nu is span T(V_(nu/p)) when nu is divisible by p and zero otherwise. The quotient is graded. For v homogeneous of nonzero weight nu, express its coset using only the b_j of weight nu by projecting any given expression to weight nu. The remainder is a finite sum c_l T(w_l) with w_l homogeneous of weight nu/p, if that weight exists. Define h(nu) as the largest nonnegative integer such that every coordinate is divisible by p^h; it is finite because some coordinate is nonzero and p>=2. If h=0 the remainder vanishes. If h>0, every w_l has height h-1. Strong induction therefore writes each w_l as a finite linear combination of T^r(b_j), and additivity and sigma-semilinearity of T put v in the same iterative span. Finally decompose an arbitrary vector into its finite homogeneous sum. The zero space and empty family cause no exception. This proof needs no finite generation assumption or bound on the support of V; I removed that unnecessary prospective assumption rather than introducing a separate bounded-support lemma.

## Mathlib searches

Every new recorded query was run through the prescribed msearch.py command and read. Both semantic services and Loogle answered, so no outage is represented as absence. The exact records and digests are in searches.jsonl; JSON records reproduce their tool and query text. Multiple formulations were tried for both new lemmas and the item. Grep queries covered Algebra/SkewPolynomial, LinearAlgebra/Finsupp and RingTheory/GradedAlgebra, alongside wider first searches.

Read Mathlib/Algebra/SkewPolynomial/Basic.lean, especially its multiplication law and definitions, and the commutative assumptions in LinearAlgebra/FreeModule/PID.lean:98. SkewMonoidAlgebra.basisSingleOne is a coefficient basis for the ring, not a homogeneous basis for an arbitrary free skew module. LinearMap.toMvPolynomial_isHomogeneous is about polynomials of linear maps. LinearAlgebra/LinearIndependent/Basic.lean:107 and :122 were inspected: map_of_surjective_injective requires a surjective coefficient map, and map_of_injective_injective has reverse scalar compatibility j(i(r)m)=rj(m), which the forward coordinate map does not satisfy for nonsurjective sigma. Their hits therefore are not exact matches or one-line specializations. The purely inseparable field-extension lemmas have separability hypotheses and concern field elements, so are not the coordinate-vector statement. The generation searches returned commutative graded-algebra, homogeneous localization and Lie weight-chain lemmas, not the semilinear dilation assertion. No Mathlib leaf is claimed.

## Review by Q44

I read the B--E delivery-error sections in full and checked each step with its cited statement open. For the item I read local Milne p.296 and distinguished its actual Proposition 14.50 from the homogeneous refinement; the latest blueprint was read as the route, not treated as a literature proof. For each new node the available source is that same motivating Milne paragraph only: their exact assertions are agent-formulated, with the independent arguments above and the unavailable Conrad/CGP sources explicitly WANTED. No claim is made to have read those sources or a nonexistent Stacks tag.

Step 1 cites exactly the existing finite-generated-submodule freeness statement. The projections commute with k and F and hence A, so their images are finite generated. Embedding via the given A^d places both summands under that statement, without using an unrecorded Noetherian fact. It applies over arbitrary characteristic-p fields. Its basis for weight zero is automatically homogeneous.

Step 2 is the explicit coefficient calculation in the already obtained basis of N. All sums are finite. J means k-span F(N), never the bare image. Its positive-F-degree description proves dimension r directly. Decomposing inputs makes J homogeneous, so ordinary finite-dimensional linear algebra selects finitely many homogeneous quotient basis vectors and homogeneous lifts. This is elementary linear algebra, not an application of the much stronger target theorem.

Step 3 cites only the new generation lemma. I checked its complete hypotheses: zero-weight component of N is zero, p is prime positive hence at least two, F is additive and c^p-semilinear by the left module law, F multiplies weights by p, and the quotient is exactly by its k-spanned image. The cited statement gives generation under iterates, which is precisely A-generation after expanding a polynomial coefficient. It does not supply independence or the zero-weight case.

Step 4 cites only the new coefficient-embedding independence lemma. A free-module coordinate vector has finite support indexed by the basis coordinate and F-exponent; F is coefficientwise c->c^p followed by an injective shift. Frobenius is an injective ring map over any field, including imperfect fields. The lemma's conclusion gives independence over the whole k, not merely over k^p. I corrected the tempting but false shortcut that injectivity of an arbitrary semilinear map alone preserves independence; that conclusion needs this special free-coordinate description.

Step 5 is a finite induction. Reducing a relation modulo J removes the constant-F coefficients. Applying step 4 to the preceding finite independent family removes the rest; no coefficient root is needed. Every A-relation is such a finite k-relation. Direct-sum assembly then gives a basis, and the coefficient calculation of the quotient M/span F(M) proves that its cardinality is d, with no unmentioned invariant-basis-number theorem. Every step/node quote in citations.json is copied verbatim from its statement, not from its proof. proof_deps is exactly the union of uses. Each proof step has fewer than 2000 characters; the two substantive independent subclaims have already been made statement-only nodes.

Edge cases checked: d=0 yields zero summands and empty bases; s=0 leaves only M_0 and N=0; an arbitrary zero-weight summand needs no Nakayama claim; positive and negative lattice coordinates both have finite p-divisibility height. For the generation lemma s=0 forces V=0. The empty lifting family implies V=0 by the same induction. The example k=F_p(t), M=A and F(M) consisting of shifted terms with coefficients in k^p shows why using the k-span is essential. Arbitrary injective semilinear maps are insufficient: on k^2 over F_p(t), T(a,b)=a^p+t b^p is injective into k but sends two independent basis vectors to dependent vectors; this does not meet the free-coordinate hypothesis of step 4. For coefficient independence, empty families and empty coordinate sets work, and no surjectivity assumption is hidden. The original item is true and requires no STATEMENT-DISPUTED correction.

## Unfinished work

No part of this one-level split remains unwritten. The two new nodes are deliberately unsplit and have empty proof/proof_deps as required; their arguments above are for later workers. Stage 2 and Lean work are outside authorization.
