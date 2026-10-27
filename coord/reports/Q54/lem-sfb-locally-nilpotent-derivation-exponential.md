# Worker report: lem-sfb-locally-nilpotent-derivation-exponential

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-locally-nilpotent-derivation-exponential.json: item, statement unchanged, split into four finite algebraic arguments.
- dag/nodes/sec-six-functors-basics/lem-sfb-lie-derivation-iterate-binomial.json: one new statement, Mathlib leaf, LieDerivation.iterate_apply_lie' at Mathlib/Algebra/Lie/Derivation/Basic.lean:145 (antidiagonal version at 133).
- citations.json: one verbatim statement excerpt for each of the three proof-step citations.

## Attachments

None. Searches of lean/WeilConjectures by the item tag, locally nilpotent, derivation and exponential found no project declaration stating the item. The project Lie files concern Engel, Cartan and solvability, not this pointwise exponential. No Lean was written or compiled.

## WANTED

WANTED: J.-P. Serre, Complex Semisimple Lie Algebras, Chapter VI appendix, reflection construction, for lem-sfb-locally-nilpotent-derivation-exponential (inherited missing source). The proof delivered here is explicitly agent-written; Milne does not state the arbitrary-dimensional pointwise exponential lemma.

## Findings and route

The item is mathematically correct, including arbitrary dimension. Its imported Mathlib candidate is only the globally nilpotent case, so it cannot be promoted to a leaf. The local/global distinction can be tested on the abelian Lie algebra Q[t] with D=d/dt: every polynomial is killed by some power, but D^n(t^n)=n! is nonzero for every n. I retained the existing searches, added the actual logged Q54 searches, and read their hits. Two distinct semantic queries for the item still found only globally nilpotent exponential results. The new leaf has its own leanfinder, loogle, grep and leansearch queries, preserved exactly from searches.jsonl; all four services succeeded. The higher Leibniz identity does not require nilpotence at all.

Read the recorded chapter/unit and the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images proof. The unit record is an older version in a different chapter; I did not alter it. This item is a deep algebraic prerequisite on the existing stable-curve/moduli/root-datum/Serre/reflection branch; it changes none of that route. tools/blueprint_refs.py ancestor returns None because this inherited branch has no current blueprint ancestor. The existing null from.node and the inherited via chain are retained; the new leaf prepends the item. Searches of the whole imported blueprint for derivation, exponential and Leibniz found no equivalent item or new leaf. The current latest Lie definition agrees with the cited definition node.

## Not duplicates

lem-sfb-lie-derivation-iterate-binomial vs lem-sfb-locally-nilpotent-derivation-exponential: the new node is a finite higher-Leibniz identity for any derivation, with no exponential, nilpotence or invertibility conclusion; it is a genuine Mathlib prerequisite, not a renamed clause of the item.
lem-sfb-lie-derivation-iterate-binomial vs lem-sfb-integrable-sl2-reflection-automorphism: the latter concerns the three sl2 exponentials and their action on weights, and depends on the item, so it cannot supply the general higher-Leibniz input.
lem-sfb-lie-derivation-iterate-binomial vs lem-sfb-sl2-divided-straightening: the latter is the opposite-root divided-power identity in an associative algebra, not powers of an arbitrary Lie derivation on a bracket.
lem-sfb-lie-derivation-iterate-binomial vs lem-sfb-associative-jacobson-identities: the latter is a prime-characteristic associative p-power formula, not the characteristic-zero general Lie-derivation identity.
lem-sfb-lie-derivation-iterate-binomial vs lem-trf-formal-relative-derivation-expansion: the latter is a first-derivative chain rule for complete power-series rings, not higher Lie derivatives.

No Stacks tag is assigned to the new leaf: its exact primary source is the Mathlib theorem read at lines 132-148. The DAG keyword/declaration searches also found Chevalley representation, Weyl-sign, rank-two straightening, Verma, restricted differentiation, restricted PBW, and distribution comparison nodes. I read their statements; all impose special root/restricted/representation data and none states the arbitrary-derivation higher-Leibniz formula. The formal class-two exponential and formal log/exp inverse nodes concern formal series and do not give the pointwise map here. No new general exponential node was created.

## Review by Q54

I read Milne's Theorem 23.63 first proof on printed pp.503-504 (PDF pp.515-516), and p.508 (PDF p.520) stating the characteristic-zero extension. This confirms the inherited Serre-presentation motivation, but supplies no proof of the local exponential assertion; accordingly proof_origin.by is agent. I read the new leaf's actual source Mathlib/Algebra/Lie/Derivation/Basic.lean:43-48,132-148 and the tempting exp construction at 401-426. The Mathlib Leibniz convention D[x,y]=[x,Dy]-[y,Dx] is exactly our convention after skew symmetry, and taking R=Q adds no hypotheses. Its natural scalar binomial coefficient has the same action as the rational coefficient. The leaf is strictly smaller than the item and is searched, rather than another unfinished theorem reproducing the exponential conclusion.

For step 1 I checked that each allowed cutoff is at least one, that all larger powers vanish by composition and linearity, and that a common maximum annihilates x, y, and ax+by. This establishes independence and linearity directly from the hypotheses, with no uniform bound. The induction (-D)^n=(-1)^n D^n verifies local nilpotence for the proposed inverse without an additional theorem. These are elementary facts and were kept as steps, not new nodes.

Step 2 cites only the new leaf. I compared its complete statement to the formula used: it applies to the given rational linear derivation without dimension or nilpotence assumptions. With annihilating bounds r,s, the pigeonhole inequality on i and r+s-i makes each term vanish, so r+s really is a valid bracket cutoff. This is where the non-elementary higher Leibniz input is used, and it has a node rather than a bare source reference.

Step 3 uses the formula already established in step 2, rational factorial arithmetic, finite reindexing, and the bilinearity explicitly stated by def-wf-lie-algebra. I opened that node and the latest blueprint definition and copied its bilinearity sentence verbatim into citations.json. Every pair i<r,j<s satisfies i+j<r+s; every omitted term has a zero factor. Thus extending the triangular sum to precisely this rectangle is justified, including r=s=1. Factoring the double sum is two applications of bilinearity, not an unproved comparison theorem.

Step 4 first proves that the output of either exponential is killed by the SAME D^N, so the outer truncation is legitimate. In the two N-by-N finite sums, terms of degree at least N vanish; for degree k<N all k+1 antidiagonal pairs occur. I checked both sign placements and the coefficient identity binom(k,i)/k!=1/(i!(k-i)!). The cited node lem-pur-commutative-ring-binomial-expansion explicitly gives the binomial theorem in every commutative ring. Q satisfies this hypothesis; x=-1,y=1 gives the zero sum for k>0, while k=0 is evaluated as its single term. I read add_pow at Mathlib/Data/Nat/Choose/Sum.lean:76-78 as well as the node statement, and copied the formula verbatim for the citation. This existing leaf is a generic algebraic tool with no route replacement. Both composites equal the identity, which proves the inverse and bijectivity claimed by the item.

Small cases checked: L=0, D=0, x=0, N=1, the k=0 inverse coefficient, r=s=1, an abelian Lie algebra with a two-step shift, the nonabelian Heisenberg example D=ad(e) with D^2=0, and Q[t] with zero bracket and d/dt (locally but not uniformly nilpotent). No finite-dimensionality, nonzero vector, associative multiplication on L, analytic convergence, or common bound on all of L was used. All factorial denominators are invertible in Q. No statement correction or disputed statement was needed.

Against delivery-errors B-E: the only new node is self-contained, with the derivation defined inline and Lie algebra notion attached to its existing definition; it carries no proof, correct Mathlib declaration/file/line, and only actual logged queries. Searches preceded its creation. Every cited node was opened and each use checked against its statement, not its proof. No citation uses a downstream result or creates a cycle. The sole extracted prerequisite is an existing Mathlib identity rather than a clause of this item's conclusion; all exponential work remains in the four explicit steps. No step exceeds 2000 characters (lengths 556,338,490,959), and the inverse is an explicit finite convolution, not a hidden existence or comparison lemma. No SGA source was used. Existing provenance and imported fields are retained.

## Unfinished work

None for this split. The independent maintainer review and the project-wide Lean formalization remain outside this delivery.
