# Stage-1 report: lem-sfb-algebraic-integer-root-unity-congruence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-integer-root-unity-congruence.json: item, statement unchanged, split into five steps following Milne Lemma 14.5.
- dag/nodes/sec-six-functors-basics/lem-sfb-prime-cyclotomic-degree-norm.json: new statement, unsplit; Mathlib candidates for degree and odd-prime norm, with generated-field setup and p=2 still to assemble.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-norm-preserves-integrality.json: new statement, Mathlib leaf Algebra.isIntegral_norm, Mathlib/RingTheory/Norm/Transitivity.lean:213-214.
- citations.json: verbatim statement quotations for all six proof-step citations.
- searches.jsonl: actual msearch output records, retained; mathematical verdicts in the node files.

## Attachments

None. Searches of WeilConjectures/ for the item tag, integral congruences and roots of unity found no exact finished project declaration. Mathlib declarations are not attachments.

## WANTED

None. The split follows the locally available Milne source and uses locally read Mathlib and Stacks sources. Milne's parenthetical ANT Chapter 6 is not used as an unseen source; the new prime cyclotomic node remains statement-only, with exact Mathlib candidates explicitly recorded.

## What needed repair

The imported item had no proof. Its statement agrees with Milne and remains unchanged. Milne's phrase “after raising it to a power” needed the new congruence quotient, rather than retaining the original alpha: the split writes beta as the binomial polynomial in alpha. Milne's norm argument implicitly needs beta in Q(eta), integer-valued norm, and degree p-1; these hypotheses and the integer divisibility contradiction are now explicit. The prime 2 is included in the signed formula; no application of an odd-prime norm theorem at 2 is asserted.

The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor prints None. Its exact inherited place and via chain are retained and extended for the new nodes. I read the current latest blueprint (main-20261023-1620) chapter, unit and sk-thm-sf-ctf-stability-direct-images.proof.md (3); this is an auxiliary arithmetic input in the inherited level-rigidity/alteration route, not a replacement of that route. No unit realization change is appropriate for this supporting item.

## Not duplicates

lem-sfb-prime-cyclotomic-degree-norm vs lem-sfb-finite-field-norm-minpoly: the existing node gives the general norm/minimal-polynomial formula but does not determine the degree or norm for prime cyclotomic generators.

lem-sfb-prime-cyclotomic-degree-norm vs lem-sfb-algebraic-integer-root-unity-congruence: the new statement has no congruence or integer n and gives cyclotomic arithmetic for any prime root, rather than the item's rigidity conclusion.

lem-sfb-prime-cyclotomic-degree-norm vs lem-sc-primitive-root: the latter is about existence and cyclicity of roots over an algebraically closed field, not the rational degree or norm of a specified primitive root.

lem-sfb-prime-cyclotomic-degree-norm vs lem-sfb-finite-free-ring-congruence-torsion: the latter is a torsion-rigidity statement for a finite-free ring, not cyclotomic arithmetic.

lem-sfb-field-norm-preserves-integrality vs lem-sfb-finite-field-norm-minpoly: the latter's statement does not assert integrality of the norm.

lem-sfb-field-norm-preserves-integrality vs lem-sfb-integral-minpoly-fraction-descent: the latter descends minimal-polynomial coefficients for normal domains and does not state integrality of field norms.

lem-sfb-field-norm-preserves-integrality vs lem-weil-rational-algebraic-integer: the latter assumes an element is integral and rational and concludes it is an integer; it does not prove the norm integral.

lem-sfb-field-norm-preserves-integrality vs lem-sfb-finite-normal-domain-norm-prime: the latter needs a finite domain algebra over a normal domain and includes prime-contraction assertions; the new node applies directly to an integral element in a rational field extension with no chosen finite integral algebra.

I searched all DAG titles and relevant statements, declaration names, and the whole imported blueprint through blueprint_refs.py for root of unity, cyclotomic, algebraic integer, minimal polynomial, integral polynomial, field norm, norm, primitive and integral norm. The existing integral-closure node already says integral elements form a subring, so I reused it rather than creating a polynomial-integrality node. Blueprint hits concerning Kummer roots or coefficient norms have different objects and statements. No new Stacks-tag duplicate was introduced.

## Review by O1

I read Milne, Abelian Varieties, Chapter I, Lemma 14.5, printed p.63/PDF p.69, with the preceding Proposition 14.4(b) for context. The source states exactly the item. For the prime cyclotomic node I read the same lemma's minimal-polynomial and norm sentences, and Mathlib Cyclotomic/PrimitiveRoots.lean:180,377-381,465-472, Cyclotomic/Basic.lean:469-495,941-946 and Polynomial/Cyclotomic/Roots.lean:178-191. I did not call the combined generated-field statement a leaf merely because the odd-prime formula is present: setting up its exact objects and handling 2 remain its future task. The source's formula gives degree 1 and norm -2 at p=2, and degree 2 and norm 3 at p=3; these are the correct small cases. No ambient number-field assumption is added: K may be transcendental over Q, since E is just the field generated by eta.

For the integrality-of-norm node I read Algebra.isIntegral_norm in Transitivity.lean:213-225, including its surrounding field and scalar-tower binders. R=Z, K=Q and L=E give its exact statement. I checked the determinant definition of Algebra.norm at Defs.lean:60-64. The scalar tower is canonical in characteristic zero; no unmentioned Galois, separability or normality hypothesis is required. Zero is allowed and its norm is integral; in degree one the assertion reduces to integrality of x itself.

Step 1 is explicit elementary order arithmetic: the least positive exponent exists from the given positive r; the prime divisor has positive quotient s; sj is strictly between 0 and m whenever 0<j<p. Thus it establishes precisely the order hypothesis of the new prime node without citing a hidden prime-order rigidity lemma.

Step 2 cites def-weil-pbc-integral-closure. I opened its statement: it explicitly asserts the subring property and containment of the integers, not only a definition. I also read Stacks algebra.tex, lemma-integral-closure-is-ring (Tag 00GO), and definition-integral-closure (00GP). The displayed binomial sum is a finite integer polynomial in alpha; repeated subring operations give its integrality. Dividing eta-1 by the nonzero integer n proves beta belongs to E; the same monic polynomial vanishes there by injectivity. No false claim that arbitrary integral elements of K automatically belong to E occurs.

Step 3 cites the new prime node for exactly its finite-degree and signed-norm clauses. K has characteristic zero and eta has order p by step 1, so both hypotheses hold. Step 4 cites the new Mathlib leaf to obtain integrality of the rational norm of beta, then lem-weil-rational-algebraic-integer to get b in Z. I opened that node's entire statement and its Mathlib match: taking Omega=Q supplies the required rational witness immediately. Step 5 cites lem-sfb-finite-field-norm-minpoly for precisely multiplicativity and the scalar power formula, which its statement explicitly contains. I read that node and Stacks fields.tex, definition-trace-norm (0BIF), lemma-characteristic-vs-minimal-polynomial (0BIG), and lemma-trace-and-norm-from-minimal-polynomial (0BIH). E is finite by step 3. The sign is retained until taking divisibility. From n^(p-1) dividing p, n divides p, forcing n=p; p=2 is already impossible because n>=3. For p>=3, p² divides p is impossible. This closes the original arbitrary-order case.

I checked delivery-errors B through E: all new statements introduce their objects; no proof is embedded in them; all non-elementary inputs have cited nodes; quotations in citations.json are verbatim; existing subring and norm facts were reused; the new arithmetic statement is independent of the item's congruence clause; no edge points back to the item; sources, actual search queries and unavailable-service distinctions are preserved. The full proof is under 3000 characters and no step exceeds 2000. At n=2 the excluded example zeta=-1, alpha=-1, r=2 would be a counterexample, confirming the threshold matters. At r=1 or alpha=0 the conclusion holds directly. No statement dispute was found.

## Unfinished work

No gap in the item's assembly remains. The new prime cyclotomic node is deliberately unsplit as required for a new non-leaf. No Lean files, repository files or launcher files were written, and no compiler or build was run.
