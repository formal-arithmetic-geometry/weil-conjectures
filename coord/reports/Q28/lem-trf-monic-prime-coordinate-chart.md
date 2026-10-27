# Stage-1 report: lem-trf-monic-prime-coordinate-chart

## Files written

- dag/nodes/sec-trace-formula/lem-trf-monic-prime-coordinate-chart.json: statement, split; no exact Mathlib match. Six explicit proof steps reuse the existing triangular-shear lemma.
- citations.json: six step/node entries, each quoting the cited statement verbatim.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written and no compiler, Lake or build command was run. All writes are in the assigned sandbox.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and for monic/prime, shear, NoetherNormalization, T_leadingcoeff_isUnit and coordinate-chart notions. The project normalization declarations do not state the prescribed triangular substitution, its explicit finite generating list, and the contracted-prime formula together. The Mathlib NoetherNormalization shear helpers are not project attachments.

## WANTED

None. Read literature/stacks-project/algebra.tex, Tag 051P, label lemma-refined-Noether-normalization (nonzero-prime part of the proof), and Tag 051N, label lemma-helper-polynomial. The tags were checked against literature/stacks-project/tags/tags. Read the current blueprint in literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/, including the ancestor lem-trf-local-term-locality.proof.md and the unit _section.md. This item refines its already-recorded algebraic route below the unit; it does not replace the contracting-correspondence proof.

## Audit of the starting node and searches

The starting statement is correct and is unchanged. Its proof was empty; the source's assertions that the map is finite and the contraction has the stated form needed explicit arguments. Its existing statement dependencies already name the polynomial-ring construction and finite-module notion used. No source error or statement dispute was found. No repair note exists for this item.

Whole-DAG searches for 051P, 051N, monic finite generation and coordinate charts found the already-existing lem-trf-polynomial-shear-leading-coefficient. Read its complete statement before using it. The finite-polynomial-coordinate-lift and normalized-polynomial-prime-lift statements concern different maps or later steps and are not needed. The broader refined-noether-normalization-prime is the item's parent and cannot be cited here. Blueprint searches for 051P, monic prime and coordinate chart produced no equivalent blueprint statement, so same_as remains empty. Retained the original blueprint ancestry and specified which algebraic part of its recorded route is realized.

Five new searches were run through the required msearch command and recorded in searches.jsonl: LeanFinder twice, Loogle, LeanSearch, and source grep. Their exact query texts and hit summaries are appended to the item's mathlib_searches; the older searches in the copied item are preserved as provenance, not presented as new Q28 searches. All five services returned successfully. Read Mathlib/RingTheory/NoetherNormalization.lean at T1 and the private leading-coefficient helper; these do not supply the full prime-coordinate chart. Read Mathlib/RingTheory/Spectrum/Prime/Polynomial.lean at exists_image_comap_of_monic, whose conclusion is a spectral image statement. Read Mathlib/RingTheory/Ideal/MonicSpan.lean at exists_monic_span_sup_map_eq, which assumes a maximal contracted ideal and concerns a different ideal decomposition. The general ordinary normalization and quasi-finite results in the second LeanFinder response likewise do not give the required map with all its clauses. Hence this item is not a Mathlib leaf.

## Unfinished work

No mathematical work remains within this item's stage-1 scope. The reused shear lemma is an existing dependency, not a newly created unsplit assertion. Delivery and its independent maintainer review remain to be recorded by the standard tools.

## Not duplicates

No new node is created. The existing 051N shear statement is cited directly instead of duplicated. The finite-generation and constant-term calculations are elementary proof steps rather than separate nodes.

## Review by Q28

I checked the six steps against the nonzero-prime paragraph of Stacks 051P and the polynomial helper 051N. The source says the chosen relation is nonconstant, changes variables to make it monic, declares the resulting map finite, and identifies its contracted prime. The proof now includes the missing intermediate calculations rather than using these source assertions as unnamed lemmas. The only non-elementary invoked result is precisely the existing 051N shear lemma. There are no new statement-only nodes whose hypotheses need separate review.

Step 1 uses the statement of lem-trf-polynomial-shear-leading-coefficient: it provides positive exponents, positive top degree and the displayed scalar-leading-term formula. Its nonconstancy hypothesis holds because a nonzero constant in a polynomial ring over a field is a unit and cannot lie in a proper prime. Nonzero g rules out the remaining constant zero. This step does not infer the prime or finite-map conclusions from that helper.

Step 2 uses def-weil-pbc-mv-polynomial-ring, whose statement actually gives evaluation homomorphisms and uniqueness from generator images. Both inverse substitutions are checked on every variable; the last variable is fixed. Scalar normalization is valid because the coefficient a is nonzero in a field. The leading coefficient becomes 1 and d is positive by Step 1. The prime-image verification in Step 3 is written directly from the ideal and prime axioms via the inverse automorphism; f belongs to the image prime by closure under multiplication by a scalar. It cites no theorem silently.

Step 4 uses the same polynomial-ring definition for evaluation, finite monomial expansions and reindexing coefficient polynomials. It also uses def-weil-finitely-generated-module, whose statement says exactly that a finite spanning list is finiteness. The relation for x_n^d is written with coefficients in the image of C. The strong induction has its base m<d and, for m>=d, only exponents m-d and m-d+j, all strictly smaller than m; it is not a circular assertion of integrality or a use of the theorem finite type plus integral implies finite. Each polynomial then lies in the span by a finite sum of its coefficients times the already-reduced powers. This is one elementary recurrence argument, with no general comparison or hidden lemma.

Step 5 again uses the polynomial-ring definition, specifically its evaluation formula. Primality of the preimage is proved from multiplication, properness and the primality already established in Step 3. The finite sum for psi(H) differs from its constant term by a multiple of f in q*. Subtracting that multiple proves both directions of the membership equivalence. Step 6 uses the same definition for H=H(0)+y_n Q and evaluation at zero. Evaluation sends every finite sum of multiples of elements of p into p, so the reverse ideal inclusion is also justified. No maximality of p or injectivity of psi is assumed.

I checked all six citation quotes against the current repository statements; each is a verbatim substring (the full statement), and each step uses only what that statement supplies. proof_deps is exactly the union of uses. No off-route theorem tool is invoked; the three cited nodes are either the item's algebraic shear ingredient or definition nodes. All six steps are shorter than 2000 characters, and none packages a new non-elementary subclaim into prose.

For edge cases I checked n=1: the shear list is empty, B=k, the proper contracted ideal p is zero, and H(f) lies in q exactly when its scalar constant term is zero. For d=1 the list is just 1 and the recurrence reduces x_n to an element in the image of C. A concrete example k=F_2, n=2, q=(x_1), g=x_1 admits e_1=1, f=x_1+x_2 and q*=(x_1+x_2); p=0 and contraction is (y_2), agreeing with the formula even in positive characteristic. The proof uses no infinite-field or separability assumption. A nonzero constant g, zero g and n=0 are excluded exactly by the hypotheses; higher powers g in the prime cause no change because only membership, not irreducibility of g, is used. The statement and the source route need no correction.
