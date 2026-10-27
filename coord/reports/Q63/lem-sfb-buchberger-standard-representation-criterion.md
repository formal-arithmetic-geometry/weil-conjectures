# Q63 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-buchberger-standard-representation-criterion.json: item, statement unchanged, six complete proof steps, status split. Mathlib searches found related division and S-polynomial results but no one-line criterion.
- dag/nodes/sec-six-functors-basics/lem-sfb-monomial-order-leading-product.json: one new statement, Mathlib leaf. The exponent clause is MonomialOrder.degree_mul, Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean:527--531; the coefficient clause is MonomialOrder.leadingCoeff_mul, same file:534--540.
- citations.json: verbatim statement quotations for every step citation.
- searches.jsonl: command-generated search audit, retained unchanged.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, Buchberger, Groebner, sPolynomial and monomial-order leading-product names found no declaration stating the item or the new leaf. The isolated hits for univariate leading coefficients do not concern this item.

## Literature wanted

WANTED: literature/lekili-commutative-algebra-lecture07-buchberger.html, Lecture 7 Theorem 4.11 and Lemma 4.12, for lem-sfb-buchberger-standard-representation-criterion. The primary page https://lekili.duckdns.org/teaching/calg/lec07.html was read online; it is not available locally. The proof is marked agent, as required, and adapts its finite-family argument to arbitrary families through finite representations. No Stacks tag is asserted for this criterion or for the Mathlib product leaf.

## Issues found

No statement dispute. No source error is needed for the monic criterion. The lecture theorem is stated for a finite generating list and zero division remainder, whereas the item's hypothesis gives strict representations for an arbitrary family. The proof uses only the strict inequalities, and each replacement still has finite support; it never assumes a finite family closed under all chosen pair representations. In particular one cannot simply restrict B to the finite family occurring initially and apply the lecture theorem, because pair representations could use other members of B. The delivered proof avoids that gap by minimizing over all finite representations in the full B.

The inherited blueprint.from.node is null, and tools/blueprint_refs.py ancestor returns None. I retained the inherited from.node, place and via chain, and the new leaf extends the chain by the item. The latest blueprint unit and its direct-image proof were read under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. This generic algebra input supports the previously recorded Groebner prerequisite; no unit or chapter route is changed.

## Unfinished work

None for the stage-1 split. The new node is already a Mathlib leaf. No Lean was written or compiled and no repository or launcher file was edited.

## Not duplicates

No existing node shares a Stacks tag with the new node: its source is Mathlib and has no Stacks tag. Whole-DAG statement searches for leading exponents, leading monomials, leading coefficients, product and multiplicativity, and searches for MonomialOrder.degree_mul and MonomialOrder.leadingCoeff_mul found no statement of this product theorem. Blueprint searches for Buchberger, leading monomial, monomial order, leading exponent, leading coefficient, degree_mul, and leading exponent product found no duplicate; the broad leading-coefficient query returned unrelated Hilbert degree and Frobenius trace nodes.

lem-sfb-monomial-order-leading-product vs lem-sfb-monomial-order-polynomial-division: the existing leaf gives a division representation with a reduced remainder; it does not state multiplication of leading exponents or coefficients.
lem-sfb-monomial-order-leading-product vs lem-sfb-bounded-homogeneous-groebner-degree: the existing statement is a uniform degree bound for initial ideals, and depends on the current item; it neither states nor replaces the elementary product formula.
lem-sfb-monomial-order-leading-product vs lem-trf-regular-hilbert-coefficient-data: that statement concerns specially chosen formal generators and division-adapted geometric data in characteristic zero, not leading-term multiplication for arbitrary polynomials over a field.
lem-sfb-monomial-order-leading-product vs lem-trf-monotone-diagram-face-exceptions: that statement is a combinatorial finiteness bound for monotone diagrams, not a polynomial product theorem. These two nodes appeared only because their proof/source text mentions related Mathlib material.

## Review by Q63

I read the complete converse proof of Theorem 4.11 and the statement and proof of Lemma 4.12 on Lekili's primary Lecture 7 page. Its argument strips off the terms at the largest exponent, rewrites their cancellation by S-polynomials, and lowers that exponent. I kept this argument in the item. Rather than creating a new node restating the criterion or its replacement step, step 4 writes the cancellation as a distributive identity using a single fixed index j and the equality that the top coefficients sum to zero. That identity takes only a few lines and uses no hidden cancellation lemma. I read the pinned Mathlib source for the new leaf, particularly degree_mul:527 and leadingCoeff_mul:534, and checked the nonzero hypotheses, the NoZeroDivisors instance supplied by a field, and the identification of finite exponent tuples with finitely supported functions on Fin r.

Step 1 cites the polynomial-ring definition, whose statement explicitly says that polynomials are finite linear combinations of monomials and gives the coefficientwise addition and bilinear multiplication. Its finite-span characterization of (B) is proved there by checking ideal closure and the least-ideal property, rather than assuming an uncited ideal-membership theorem. Step 2 cites the same definition: translating a support is justified by the displayed monomial multiplication law and the assumed addition compatibility of the order; finite sums introduce no new exponent. Choosing the least maximum uses exactly the well-order hypothesis of the item. Step 3 cites no node: it compares the coefficient at delta, and obtains sum c_i=0 because monicity makes the coefficient of each maximal summand exactly c_i. Step 4 again uses the polynomial-ring multiplication law; both leading exponents are coordinatewise bounded by delta before any truncated subtraction is used. Expanding the two summands of P proves the stated identity. These cited definitions say exactly what is used, and all needed arguments beyond their literal definitions are written in the steps.

Step 5 cites only the new product leaf. Its first clause gives LM(q u)=LM(q)+LM(u); its second clause, together with nonzero leading coefficients and the field hypothesis, ensures q u is nonzero when q is nonzero. For each support exponent beta, beta is at most LM(q); adding LM(u) and then delta-lambda preserves the inequalities, and the coordinatewise lambda<=delta checked in step 4 makes their sum delta. The strict bound comes from the item's hypothesis, not from a hidden division theorem or from a node's proof. Step 6 cites the polynomial-ring definition for the final monomial expansion. Its finite-support calculation includes every chosen pair representation, so the new finite list is valid even when B is infinite, and its nonempty finite maximum contradicts the explicit minimization of step 2. Every citation is reproduced verbatim from its statement in citations.json; no cited node is used for a claim appearing only in its proof.

I tested the empty set (zero ideal), singleton B (a top cancellation cannot have a lone nonzero coefficient), B containing 1 (leading exponent 0 and divisibility immediate), repeated generators in a representation (the corresponding P is zero), zero S-polynomials (zero representations suffice), positive characteristic (sum c_i=0 is used without division or a characteristic assumption), and lex orders not compatible with total degree (only addition compatibility is used). In the delta=0 case every exponent is 0, so the lower-exponent alternative is impossible and no undefined leading exponent of zero is introduced. The leaf states LM only for nonzero products and defines LC(0) for its unrestricted coefficient clause. I compared against delivery-errors B--E: all objects and notions are introduced, no source tag is misidentified, the new node has no proof, searches were genuinely run and logged, the leaf uses one declaration per clause with source lines, and no clause of the item was moved into a new unsplit node. All proof steps are under 2000 characters. The one non-elementary multiplication theorem is cited, while coefficient comparisons, finite sums, the well-order minimum, and the displayed cancellation identity are explicit elementary steps.
